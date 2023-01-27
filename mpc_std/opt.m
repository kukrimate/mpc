/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 *
 * Description: Maybe monad
 */

import prog

enum Option<T>(
  Some (val: T),
  None
)

function some<T>(val: T) -> Option<T> {
  Option::Some(val)
}

function none<T>() -> Option<T> {
  Option::None
}

function unwrap<T>(o: Option<T>) -> T {
  match o {
    s: Some => s.val,
    None    => prog::panic(c"Tried to unwrap None\n")
  }
}
