/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 */

use std::collections::HashSet;
use std::error::Error;
use std::fmt;
use std::os::raw::c_char;
use std::sync::Mutex;

/// Boxed, type-erased error wrapper

pub type MRes<T> = Result<T, Box<dyn Error + Send + Sync>>;

/// Globally de-duped strings

static STRING_TABLE: Mutex<Option<HashSet<&'static str>>> = Mutex::new(None);

fn string_table_intern(s: &str) -> &'static str {
  let s = to_owned_c(s);
  let mut locked = STRING_TABLE.lock().unwrap();
  locked
    .get_or_insert_with(|| HashSet::new())
    .get_or_insert(Box::leak(s))
}

fn to_owned_c(s: &str) -> Box<str> {
  let mut s = str::to_owned(s);
  s.push('\0');
  s.into_boxed_str()
}

#[derive(Clone, Copy)]
pub struct RefStr {
  s: &'static str
}

impl RefStr {
  pub fn new(s: &str) -> RefStr {
    RefStr {
      s: string_table_intern(s)
    }
  }

  pub fn borrow_rs(&self) -> &str {
    &self.s[0..self.s.len() - 1]
  }

  pub fn borrow_c(&self) -> *const i8 {
    self.s.as_ptr() as _
  }
}

impl fmt::Display for RefStr {
  fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
    self.borrow_rs().fmt(fmt)
  }
}

impl fmt::Debug for RefStr {
  fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
    self.borrow_rs().fmt(fmt)
  }
}

impl PartialEq for RefStr {
  fn eq(&self, rhs: &RefStr) -> bool {
    self.s as *const str == rhs.s as *const str
  }
}

impl Eq for RefStr {}

impl std::hash::Hash for RefStr {
  fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
    (self.s as *const str).hash(state)
  }
}

// Linear search a vector of pairs

pub fn lin_search<'vec, T: PartialEq, U>(vec: &'vec Vec<(T, U)>, want: &T) -> Option<(usize, &'vec U)> {
  for (idx, (key, val)) in vec.iter().enumerate() {
    if key == want {
      return Some((idx, val));
    }
  }
  None
}

// Write a comma seperated list of values

pub fn write_comma_separated<I, T, W>(f: &mut fmt::Formatter<'_>, iter: I, wfn: W) -> fmt::Result
  where I: Iterator<Item=T>,
        W: Fn(&mut fmt::Formatter<'_>, &T) -> fmt::Result,
{
  write!(f, "(")?;
  let mut comma = false;
  for item in iter {
    if comma {
      write!(f, ", ")?;
    } else {
      comma = true;
    }
    wfn(f, &item)?;
  }
  write!(f, ")")
}

// Empty NUL-terminated string

pub fn empty_cstr() -> *const i8 {
  b"\0".as_ptr() as _
}

/// Monadic collection over an iterator of results

pub trait MonadicCollect<O> {
  fn monadic_collect(&mut self) -> MRes<Vec<O>>;
}

impl<I, O> MonadicCollect<O> for I
  where I: Iterator<Item=MRes<O>>
{
  fn monadic_collect(&mut self) -> MRes<Vec<O>> {
    let mut vec = Vec::new();
    for item in self {
      vec.push(item?);
    }
    Ok(vec)
  }
}

pub trait MonadicCollect2<O, E> {
  fn monadic_collect2(&mut self) -> Result<Vec<O>, E>;
}

impl<I, O, E> MonadicCollect2<O, E> for I
  where I: Iterator<Item=Result<O, E>>
{
  fn monadic_collect2(&mut self) -> Result<Vec<O>, E> {
    let mut vec = Vec::new();
    for item in self {
      vec.push(item?);
    }
    Ok(vec)
  }
}

/// Calculate the length of a C-style string (in bytes)

pub unsafe fn c_strlen(s: *const c_char) -> usize {
  let mut end = s;
  while end.read() != 0 {
    end = end.add(1);
  }
  end.offset_from(s) as _
}

/// Concatenate two vectors
pub fn concat<T>(mut a: Vec<T>, b: Vec<T>) -> Vec<T> {
  a.extend(b.into_iter());
  a
}
