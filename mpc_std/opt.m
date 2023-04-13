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

function (o: *Option<T>) is_some<T>() -> Bool {
  match *o {
    Some(val) => true,
    None => false
  }
}

function (o: *Option<T>) is_none<T>() -> Bool {
  match *o {
    Some(val) => false,
    None => true
  }
}

function (o: Option<T>) unwrap<T>() -> T {
  match o {
    Some(val) => val,
    None => prog::panic(c"Tried to unwrap None\n")
  }
}
