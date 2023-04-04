/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 */

use std::collections::HashSet;
use std::fmt;
use std::mem::MaybeUninit;
use std::sync::Mutex;

/// Globally de-duped strings

static STRING_TABLE: Mutex<Option<HashSet<&'static str>>> = Mutex::new(None);

fn string_table_intern(s: &str) -> &'static str {
  let s = to_owned_c(s);
  let mut locked = STRING_TABLE.lock().unwrap();
  locked
    .get_or_insert_with(|| HashSet::new())
    .get_or_insert_with(&*s, |s| Box::leak(str::to_owned(s).into_boxed_str()))
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

/// Monadic collection over an iterator of results

pub trait MonadicCollect<O, E> {
  fn monadic_collect(&mut self) -> Result<Vec<O>, E>;
}

impl<I, O, E> MonadicCollect<O, E> for I
  where I: Iterator<Item=Result<O, E>>
{
  fn monadic_collect(&mut self) -> Result<Vec<O>, E> {
    let mut vec = Vec::new();
    for item in self {
      vec.push(item?);
    }
    Ok(vec)
  }
}

/// Concatenate two vectors
pub fn concat<T>(mut a: Vec<T>, b: Vec<T>) -> Vec<T> {
  a.extend(b.into_iter());
  a
}


/// Fixed length first-in first-out buffer
pub struct FIFO<T, const N: usize> {
  array: [MaybeUninit<T>; N],
  pos: usize,
  len: usize,
}

impl<T, const N: usize> FIFO<T, N> {
  pub fn new() -> Self {
    FIFO {
      array: unsafe { MaybeUninit::uninit().assume_init() },
      pos: 0,
      len: 0,
    }
  }

  pub fn len(&self) -> usize {
    self.len
  }

  pub fn get(&self, i: usize) -> Option<&T> {
    if i < self.len {
      Some(unsafe {
        &*self.array
          // Get reference to the ith MaybeUninit cell
          .get_unchecked((self.pos + i) % N)
          // Get pointer to the inside of the cell
          .as_ptr()
      })
    } else {
      None
    }
  }

  pub fn push(&mut self, val: T) {
    // Make sure there is room
    assert!(self.len < N);

    unsafe {
      self.array
        // Get reference to MaybeUninit cell
        .get_unchecked_mut((self.pos + self.len) % N)
        // Write value to cell
        .as_mut_ptr().write(val);
    }

    // Incrase length
    self.len += 1;
  }

  pub fn pop(&mut self) -> Option<T> {
    if self.len > 0 {
      let val = unsafe {
        self.array
          // Get reference to MaybeUninit cell
          .get_unchecked(self.pos)
          // Read value from cell
          .as_ptr().read()
      };

      // Increase position
      self.pos = (self.pos + 1) % N;
      // Decrease length
      self.len -= 1;

      Some(val)
    } else {
      // No elements to pop
      None
    }
  }
}
