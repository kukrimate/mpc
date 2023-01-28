/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 *
 * Description: Array helpers
 */

import mem

function length<T>(array: *T) -> Uintn {
  mem::size_of(array) / mem::size_of(&(*array)[0])
}
