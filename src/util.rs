use std::any::Any;
use std::collections::HashSet;
use std::error::Error;
use std::mem::MaybeUninit;

/// Boxed, type-erased error wrapper

pub type MRes<T> = Result<T, Box<dyn Error>>;

/// Globally de-duped strings

static mut STRING_TABLE: MaybeUninit<HashSet<String>> = MaybeUninit::uninit();

pub fn init() {
  unsafe { STRING_TABLE = MaybeUninit::new(HashSet::new()) }
}

#[derive(Clone, Copy)]
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

  pub fn ptr_mut(&mut self) -> PtrMut<T> {
    PtrMut(self.0)
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


// Const borrowed pointer

#[allow(dead_code)]
pub struct Ptr<T: ?Sized>(*const T);

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

impl<T: ?Sized> core::ops::Deref for Ptr<T> {
  type Target = T;

  fn deref(&self) -> &T {
    unsafe { &*self.0 }
  }
}

impl<T: ?Sized + PartialEq> PartialEq for Ptr<T> {
  fn eq(&self, rhs: &Ptr<T>) -> bool {
    unsafe { *self.0 == *rhs.0 }
  }
}

impl<T: ?Sized + Eq> Eq for Ptr<T> {}

impl<T: ?Sized + std::hash::Hash> core::hash::Hash for Ptr<T> {
  fn hash<H: core::hash::Hasher>(&self, h: &mut H) {
    unsafe { (*self.0).hash(h); }
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

// Mutable borrowed pointer

pub struct PtrMut<T: ?Sized>(*mut T);

impl<T: ?Sized> PtrMut<T> {
  pub fn ptr(&self) -> Ptr<T> {
    Ptr(self.0)
  }
}

impl<T: ?Sized> Clone for PtrMut<T> {
  fn clone(&self) -> Self {
    PtrMut(self.0)
  }
}

impl<T: ?Sized> Copy for PtrMut<T> {}

impl<T: ?Sized> core::borrow::Borrow<T> for PtrMut<T> {
  fn borrow(&self) -> &T {
    unsafe { &*self.0 }
  }
}

impl<T: ?Sized> core::borrow::BorrowMut<T> for PtrMut<T> {
  fn borrow_mut(&mut self) -> &mut T {
    unsafe { &mut *self.0 }
  }
}

impl<T: ?Sized> core::ops::Deref for PtrMut<T> {
  type Target = T;

  fn deref(&self) -> &T {
    unsafe { &*self.0 }
  }
}

impl<T: ?Sized> core::ops::DerefMut for PtrMut<T> {
  fn deref_mut(&mut self) -> &mut T {
    unsafe { &mut *self.0 }
  }
}

impl<T: ?Sized + PartialEq> PartialEq for PtrMut<T> {
  fn eq(&self, rhs: &PtrMut<T>) -> bool {
    unsafe { *self.0 == *rhs.0 }
  }
}

impl<T: ?Sized + Eq> Eq for PtrMut<T> {}

impl<T: ?Sized + std::hash::Hash> core::hash::Hash for PtrMut<T> {
  fn hash<H: core::hash::Hasher>(&self, h: &mut H) {
    unsafe { (*self.0).hash(h); }
  }
}

impl<T: ?Sized + std::fmt::Display> std::fmt::Display for PtrMut<T> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
    unsafe { (*self.0).fmt(f) }
  }
}

impl<T: ?Sized + std::fmt::Debug> std::fmt::Debug for PtrMut<T> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
    unsafe { (*self.0).fmt(f) }
  }
}

// "Arena" allocator
// NOTE: this could be a lot more efficient if we actually allocated from
// contigous memory buckets

pub struct Arena(Vec<Own<dyn Any>>);

impl Arena {
  pub fn new() -> Self {
    Arena(Vec::new())
  }

  pub fn alloc<T: 'static>(&mut self, val: T) -> PtrMut<T> {
    let raw = Own::new(val).into_raw();
    self.0.push(Own(raw));
    PtrMut(raw)
  }
}
