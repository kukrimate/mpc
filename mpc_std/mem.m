/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 *
 * Description: Standard memory utilities
 */

import libc

function zero_bytes<T>(ptr: *mut T, n: Uintn) {
  libc::memset(ptr as <*mut libc::Void>, 0, n);
}

function copy_bytes<T>(to: *mut T, from: *T, n: Uintn) {
  libc::memmove(to as <*mut libc::Void>, from as <*libc::Void>, n);
}
