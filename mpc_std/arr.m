/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 *
 * Description: Array helpers
 */

import mem

function length<T, U>(array: *T) -> Uintn {
  let _: *U = &(*array)[0];
  mem::size_of::<T>() / mem::size_of::<U>()
}
