/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 *
 * Description: Either monad
 */

import prog

enum Result<O, E> (
  Ok(v: O),
  Err(v: E)
)

function (result: *Result<O, E>) is_ok<O, E>() -> Bool {
  match *result {
    Ok(v) => true,
    Err(v) => false
  }
}

function (result: *Result<O, E>) is_err<O, E>() -> Bool {
  match *result {
    Ok(v) => false,
    Err(v) => true
  }
}

function (result: Result<O, E>) unwrap_ok<O, E>() -> O {
  match result {
    Ok(v) => v,
    Err(v) => prog::panic(c"Value required instead of error\n")
  }
}

function (result: Result<O, E>) unwrap_err<O, E>() -> E {
  match result {
    Ok(v) => prog::panic(c"Error required instead of value\n"),
    Err(v) => v
  }
}
