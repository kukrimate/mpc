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

function ok<O, E>(v: O) -> Result<O, E> {
  Result::Ok(v)
}

function err<O, E>(v: E) -> Result<O, E> {
  Result::Err(v)
}

function is_ok<O, E>(result: *Result<O, E>) -> Bool {
  match *result {
    Ok => true,
    Err => false
  }
}

function is_err<O, E>(result: *Result<O, E>) -> Bool {
  match *result {
    Ok => false,
    Err => true
  }
}

function unwrap_ok<O, E>(result: Result<O, E>) -> O {
  match result {
    ok: Ok => ok.v,
    Err => prog::panic(c"Value required instead of error\n")
  }
}

function unwrap_err<O, E>(result: Result<O, E>) -> E {
  match result {
    Ok => prog::panic(c"Error required instead of value\n"),
    err: Err => err.v
  }
}
