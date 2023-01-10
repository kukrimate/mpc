/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 */

use std::collections::HashSet;
use std::error::Error;
use std::fmt;
use std::os::raw::c_char;

/// Same thing std uses for pretty printing
/// This should really be an exposed API :(

pub struct PadAdapter<'buf> {
  buf: &'buf mut (dyn fmt::Write + 'buf),
  state: PadAdapterState,
}

struct PadAdapterState {
  on_newline: bool,
}

impl Default for PadAdapterState {
  fn default() -> Self {
    PadAdapterState { on_newline: true }
  }
}

impl<'buf> PadAdapter<'buf> {
  pub fn wrap(fmt: &'buf mut fmt::Formatter<'_>) -> Self {
    PadAdapter {
      buf: fmt,
      state: Default::default(),
    }
  }
}

impl fmt::Write for PadAdapter<'_> {
  fn write_str(&mut self, s: &str) -> fmt::Result {
    for s in s.split_inclusive('\n') {
      if self.state.on_newline {
        self.buf.write_str("  ")?;
      }
      self.state.on_newline = s.ends_with('\n');
      self.buf.write_str(s)?;
    }
    Ok(())
  }
}

/// Boxed, type-erased error wrapper

pub type MRes<T> = Result<T, Box<dyn Error>>;

/// Globally de-duped strings

static mut STRING_TABLE: Option<HashSet<String>> = None;

fn string_table_mut() -> &'static mut HashSet<String> {
  unsafe {
    if let Some(val) = STRING_TABLE.as_mut() {
      val
    } else {
      STRING_TABLE.insert(HashSet::new())
    }
  }
}

#[derive(Clone, Copy)]
pub struct RefStr {
  s: &'static str
}

impl RefStr {
  pub fn new(s: &str) -> RefStr {
    let s = to_owned_c(s);
    RefStr {
      s: string_table_mut().get_or_insert(s)
    }
  }

  pub fn borrow_rs(&self) -> &str {
    &self.s[0..self.s.len() - 1]
  }

  pub fn borrow_c(&self) -> *const i8 {
    self.s.as_ptr() as _
  }
}

fn to_owned_c(s: &str) -> String {
  let mut s = str::to_owned(s);
  s.push('\0');
  s
}

impl std::fmt::Display for RefStr {
  fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
    self.borrow_rs().fmt(fmt)
  }
}

impl std::fmt::Debug for RefStr {
  fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
    self.borrow_rs().fmt(fmt)
  }
}

impl std::cmp::PartialEq for RefStr {
  fn eq(&self, rhs: &RefStr) -> bool {
    self.s as *const str == rhs.s as *const str
  }
}

impl std::cmp::Eq for RefStr {}

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

/// Calculate the length of a C-style string (in bytes)

pub unsafe fn c_strlen(s: *const c_char) -> usize {
  let mut end = s;
  while end.read() != 0 {
    end = end.add(1);
  }
  end.offset_from(s) as _
}
