/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 *
 * Description: Program utilities
 */

import libc

// Exit the program with exit code `code`
function exit<T>(code: Int32) -> T {
  libc::exit(code);
  exit(code)
}

// Panic the program with message `msg`
function panic<T>(msg: *Int8) -> T {
  libc::fprintf(libc::stderr, c"%s", msg);
  libc::abort();
  panic(msg)
}
