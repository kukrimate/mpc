/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 *
 * Description: String utilities
 */

import slice
import vec

type Str = vec::Vec<Uint8>
type StrView = slice::Slice<Uint8>

function view_from_lit<ArrayType>(a: *ArrayType) -> StrView {
  slice::from_array(a)
}

function view_from_str<ArrayType>(s: *Str) -> StrView {
  slice::from_vec(s)
}

function eq(a: StrView, b: StrView) -> Bool {
  if a.length != b.length { return false }
  let mut i = 0;
  while i < a.length {
    if *slice::at(a, i) != *slice::at(b, i) { return false }
    i += 1;
  }
  true
}

function ne(a: StrView, b: StrView) -> Bool {
  !eq(a, b)
}
