/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 *
 * Description: Implementation of a vector data structure
 */

import mem
import opt
import prog

struct Vec<T>(mem: *mut T, length: Uintn, capacity: Uintn)

function new<T>() -> Vec<T> {
  Vec(nil, 0, 0)
}

function (vec: *mut Vec<T>) delete<T>() {
  mem::deallocate((*vec).mem)
}

function (vec: *mut Vec<T>) ensure_capacity<T>(capacity: Uintn) {
  if (*vec).capacity < capacity {
    (*vec).capacity = capacity * 2;
    (*vec).mem = mem::reallocate_contiguous((*vec).mem, capacity * 2);
  }
}

function (vec: *mut Vec<T>) push<T>(val: T) {
  ensure_capacity(vec, (*vec).length + 1);
  *mem::ptr_off((*vec).mem, (*vec).length) = val;
  (*vec).length += 1;
}

function (vec: *mut Vec<T>) at<T>(index: Uintn) -> *mut T {
  if index >= (*vec).length {
    prog::panic(c"Tried to access vec out of bounds");
  }
  mem::ptr_off((*vec).mem, index)
}

function (vec: *mut Vec<T>) at_or_none<T>(index: Uintn) -> opt::Option<*mut T> {
  if index < (*vec).length {
    opt::some(mem::ptr_off((*vec).mem, index))
  } else {
    opt::none()
  }
}

function (vec: *mut Vec<T>) pop<T>() -> T {
  if (*vec).length == 0 {
    prog::panic(c"Tried to pop form empty vec");
  }
  (*vec).length -= 1;
  *mem::ptr_off((*vec).mem, (*vec).length)
}

function (vec: *mut Vec<T>) pop_or_none<T>() -> opt::Option<T> {
  if (*vec).length > 0 {
    (*vec).length -= 1;
    opt::some(*mem::ptr_off((*vec).mem, (*vec).length))
  } else {
    opt::none()
  }
}
