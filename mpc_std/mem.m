/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 *
 * Description: Standard memory utilities
 */

import libc

struct AlignOfHelper<T> (byte: Uint8, val: T)
struct SizeOfHelper<T> (val: T, end: Uint8)

// Yields the minimum alignment of T in bytes
function align_of<T>() -> Uintn {
  let ptr: *AlignOfHelper<T> = nil;
  (&(*ptr).val) as <Uintn>
}

// Yields the size of T in bytes
function size_of<T>() -> Uintn {
  let ptr: *SizeOfHelper<T> = nil;
  (&(*ptr).end) as <Uintn>
}

// Allocate memory to hold one instance of T
function allocate<T>() -> *mut T {
  libc::malloc(size_of::<T>()) as <*mut T>
}

// Allocate memory to hold n instances of T
function allocate_contiguous<T>(n: Uintn) -> *mut T {
  libc::malloc(size_of::<T>() * n) as <*mut T>
}

// Resize a (potentially empty) memory block to hold n instances of T
function reallocate_contiguous<T>(ptr: *mut T, n: Uintn) -> *mut T {
  libc::realloc(ptr as <*mut libc::Void>, size_of::<T>() * n) as <*mut T>
}

// Deallocate a memory block
function deallocate<T>(ptr: *mut T) {
  libc::free(ptr as <*mut libc::Void>)
}

// Yield a pointer to the i-th element in a memory block holding instances of T
function ptr_off<T>(ptr: *mut T, i: Uintn) -> *mut T {
  (ptr as <Uintn> + i * size_of::<T>()) as <*mut T>
}

// Yield the number of instances of T held in the memory block between a and b
function ptr_diff<T>(a: *mut T, b: *mut T) -> Uintn {
  (b as <Uintn> - a as <Uintn>) / size_of::<T>()
}

function zero_bytes<T>(ptr: *mut T, n: Uintn) {
  libc::memset(ptr as <*mut libc::Void>, 0, n);
}

function copy_bytes<T>(to: *mut T, from: *T, n: Uintn) {
  libc::memmove(to as <*mut libc::Void>, from as <*libc::Void>, n);
}
