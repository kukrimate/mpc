/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 *
 * Description: String utilities
 */

import slice::Slice
import vec::Vec

struct Str(vec: Vec<Uint8>)

function (!Str) new() -> Str {
  Str(Vec::new())
}

function (s: *mut Str) push(byte: Uint8) {
  s.vec.push(byte)
}

struct StrView(slice: Slice<Uint8>)

function (!StrView) from_lit<ArrayType>(a: *ArrayType) -> StrView {
  StrView(Slice::from_array(a))
}

function (!StrView) from_str<ArrayType>(s: *Str) -> StrView {
  StrView(Slice::from_vec(&s.vec))
}

function (a: StrView) eq(b: StrView) -> Bool {
  if a.slice.length != b.slice.length { return false }
  let mut i = 0;
  while i < a.slice.length {
    if *a.slice.at(i) != *b.slice.at(i) { return false }
    i += 1;
  }
  true
}

function (a: StrView) ne(b: StrView) -> Bool {
  !a.eq(b)
}
