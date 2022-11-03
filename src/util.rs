use std::collections::HashSet;
use std::error::Error;
use std::fmt;
use std::mem::MaybeUninit;

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

static mut STRING_TABLE: MaybeUninit<HashSet<String>> = MaybeUninit::uninit();

pub fn init() {
  unsafe { STRING_TABLE = MaybeUninit::new(HashSet::new()) }
}

fn to_owned_c(s: &str) -> String {
  let mut s = str::to_owned(s);
  s.push('\0');
  s
}

#[derive(Clone, Copy)]
pub struct RefStr {
  s: &'static str
}

impl RefStr {
  pub fn new(s: &str) -> RefStr {
    let s = to_owned_c(s);
    unsafe {
      RefStr {
        s: STRING_TABLE.assume_init_mut().get_or_insert(s)
      }
    }
  }

  pub fn borrow_rs(&self) -> &str {
    &self.s[0..self.s.len() - 1]
  }

  pub fn borrow_c(&self) -> *const i8 {
    unsafe { std::mem::transmute(&self.s.as_bytes()[0] as *const u8) }
  }
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

/// Owning pointer

#[allow(dead_code)]
pub struct Own<T: ?Sized>(*mut T);

impl<T> Own<T> {
  pub fn new(val: T) -> Self {
    Own(Box::into_raw(Box::new(val)))
  }
}

impl<T: ?Sized> Own<T> {
  fn into_raw(self) -> *mut T {
    let raw = self.0;
    std::mem::forget(self);
    raw
  }

  pub fn ptr(&self) -> Ptr<T> {
    Ptr(self.0)
  }
}

impl<T: ?Sized> From<Box<T>> for Own<T> {
  fn from(val: Box<T>) -> Self {
    Own(Box::into_raw(val))
  }
}

impl<T: ?Sized> Drop for Own<T> {
  fn drop(&mut self) {
    unsafe { drop(Box::from_raw(self.0)); }
  }
}

impl<T: ?Sized> core::borrow::Borrow<T> for Own<T> {
  fn borrow(&self) -> &T {
    unsafe { &*self.0 }
  }
}

impl<T: ?Sized> core::borrow::BorrowMut<T> for Own<T> {
  fn borrow_mut(&mut self) -> &mut T {
    unsafe { &mut *self.0 }
  }
}

impl<T: ?Sized> core::ops::Deref for Own<T> {
  type Target = T;

  fn deref(&self) -> &T {
    unsafe { &*self.0 }
  }
}

impl<T: ?Sized> core::ops::DerefMut for Own<T> {
  fn deref_mut(&mut self) -> &mut T {
    unsafe { &mut *self.0 }
  }
}

impl<T: ?Sized + PartialEq> PartialEq for Own<T> {
  fn eq(&self, rhs: &Own<T>) -> bool {
    unsafe { *self.0 == *rhs.0 }
  }
}

impl<T: ?Sized + Eq> Eq for Own<T> {}

impl<T: ?Sized + std::hash::Hash> core::hash::Hash for Own<T> {
  fn hash<H: core::hash::Hasher>(&self, h: &mut H) {
    unsafe { (*self.0).hash(h); }
  }
}

impl<T: ?Sized + std::fmt::Display> std::fmt::Display for Own<T> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
    unsafe { (*self.0).fmt(f) }
  }
}

impl<T: ?Sized + std::fmt::Debug> std::fmt::Debug for Own<T> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
    unsafe { (*self.0).fmt(f) }
  }
}

// Borrowed pointer

pub struct Ptr<T: ?Sized>(*mut T);

impl<T: ?Sized> Clone for Ptr<T> {
  fn clone(&self) -> Self {
    Ptr(self.0)
  }
}

impl<T: ?Sized> Copy for Ptr<T> {}

impl<T: ?Sized> core::borrow::Borrow<T> for Ptr<T> {
  fn borrow(&self) -> &T {
    unsafe { &*self.0 }
  }
}

impl<T: ?Sized> core::borrow::BorrowMut<T> for Ptr<T> {
  fn borrow_mut(&mut self) -> &mut T {
    unsafe { &mut *self.0 }
  }
}

impl<T: ?Sized> core::ops::Deref for Ptr<T> {
  type Target = T;

  fn deref(&self) -> &T {
    unsafe { &*self.0 }
  }
}

impl<T: ?Sized> core::ops::DerefMut for Ptr<T> {
  fn deref_mut(&mut self) -> &mut T {
    unsafe { &mut *self.0 }
  }
}

impl<T: ?Sized> PartialEq for Ptr<T> {
  fn eq(&self, rhs: &Ptr<T>) -> bool {
    self.0 == rhs.0
  }
}

impl<T: ?Sized> Eq for Ptr<T> {}

impl<T: ?Sized> core::hash::Hash for Ptr<T> {
  fn hash<H: core::hash::Hasher>(&self, h: &mut H) {
    self.0.hash(h);
  }
}

impl<T: ?Sized + std::fmt::Display> std::fmt::Display for Ptr<T> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
    unsafe { (*self.0).fmt(f) }
  }
}

impl<T: ?Sized + std::fmt::Debug> std::fmt::Debug for Ptr<T> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
    unsafe { (*self.0).fmt(f) }
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
  unsafe { std::mem::transmute(&b"\0"[0] as *const u8) }
}
