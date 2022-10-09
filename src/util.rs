use std::collections::HashSet;
use std::error::Error;
use std::mem::MaybeUninit;

/// Boxed, type-erased error wrapper

pub type MRes<T> = Result<T, Box<dyn Error>>;

/// Functions for doing evil stuff

pub fn evil<'a, T>(r: &'a T) -> &'static T {
  unsafe { std::mem::transmute(r) }
}

pub fn evil_mut<'a, T>(r: &'a mut T) -> &'static mut T {
  unsafe { std::mem::transmute(r) }
}

/// Globally de-duped strings

static mut STRING_TABLE: MaybeUninit<HashSet<String>> = MaybeUninit::uninit();

pub fn init() {
  unsafe { STRING_TABLE = MaybeUninit::new(HashSet::new()) }
}

#[derive(Clone,Copy)]
pub struct RefStr {
  s: &'static str
}

impl RefStr {
  pub fn new(s: &str) -> RefStr {
    unsafe {
      RefStr {
        s: STRING_TABLE.assume_init_mut().get_or_insert_with(s, str::to_owned)
      }
    }
  }
}

impl core::borrow::Borrow<str> for RefStr {
  fn borrow(&self) -> &str {
    self.s
  }
}

impl std::fmt::Display for RefStr {
  fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
    self.s.fmt(fmt)
  }
}

impl std::fmt::Debug for RefStr {
  fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
    self.s.fmt(fmt)
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
