/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 */

// C primitive types (can differ between platform/ABIs)
struct Void()
type Char = Int8
type Uchar = Uint8
type Short = Int16
type Ushort = Uint16
type Int = Int32
type Uint = Uint32
type Long = Int64
type Ulong = Uint64
type Llong = Int64
type Ullong = Uint64

// stdio.h
struct FILE()

extern {
  function printf(fmt: *Char, ...) -> Int
  function fprintf(stream: *mut FILE, fmt: *Char, ...) -> Int
  function puts(str: *Char) -> Int

  data stdin: *mut FILE
  data stdout: *mut FILE
  data stderr: *mut FILE
}

// stdlib.h
extern {
  function atof(nptr: *Char) -> Double
  function atoi(nptr: *Char) -> Int
  function atol(nptr: *Char) -> Long
  function atoll(nptr: *Char) -> Llong

  function strtod(nptr: *Char, endptr: *mut *mut Char) -> Double
  function strtof(nptr: *Char, endptr: *mut *mut Char) -> Float
  function strtol(nptr: *Char, endptr: *mut *mut Char, base: Int) -> Long
  function strtoll(nptr: *Char, endptr: *mut *mut Char, base: Int) -> Llong
  function strtoul(nptr: *Char, endptr: *mut *mut Char, base: Int) -> Ulong
  function strtoull(nptr: *Char, endptr: *mut *mut Char, base: Int) -> Ullong

  function rand() -> Int
  function srand(seed: Uint)

  function calloc(nmemb: Uintn, size: Uintn) -> *mut Void
  function free(ptr: *mut Void)
  function malloc(size: Uintn) -> *mut Void
  function realloc(old: *mut Void, size: Uintn) -> *mut Void

  function abort()
  function atexit(func: Function()) -> Int
  function exit(status: Int)
  function _Exit(status: Int)

  function getenv(name: *Char) -> *mut Char

  function system(string: *Char) -> Int

  function bsearch(key: *Void, base: *Void,
                    nmemb: Uintn, size: Uintn,
                    compar: Function(a: *Void, b: *Void)) -> *mut Void

  function qsort(base: *mut Void,
                  nmemb: Uintn, size: Uintn,
                  compar: Function(a: *Void, b: *Void))

  function abs(j: Int) -> Int
  function labs(j: Long) -> Long
  function llabs(j: Llong) -> Llong
}

// string.h
extern {
  function memcpy(dest: *mut Void, src: *Void, len: Uintn) -> *mut Void
  function memmove(dest: *mut Void, src: *Void, len: Uintn) -> *mut Void
  function strcpy(s1: *mut Char, s2: *Char) -> *mut Char
  function strncpy(s1: *mut Char, s2: *Char, n: Uintn) -> *mut Char
  function strcat(s1: *mut Char, s2: *Char) -> *mut Char
  function strncat(s1: *mut Char, s2: *Char, n: Uintn) -> *mut Char
  function memcmp(s1: *Void, s2: *Void, n: Uintn) -> Int
  function strcmp(s1: *Char, s2: *Char) -> Int
  function strcoll(s1: *Char, s2: *Char) -> Int
  function strncmp(s1: *Char, s2: *Char, n: Uintn) -> Int
  function strxfrm(s1: *Char, s2: *Char, n: Uintn) -> Uintn
  function memchr(s: *Void, c: Int, n: Uintn) -> *mut Void
  function strchr(s: *Char, c: Int) -> *mut Char
  function strcspn(s1: *Char, s2: *Char) -> Uintn
  function strpbrk(s1: *Char, s2: *Char) -> *mut Char
  function strrchr(s: *Char, c: Int) -> *mut Char
  function strspn(s1: *Char, s2: *Char) -> Uintn
  function strstr(s1: *Char, s2: *Char) -> *mut Char
  function strtok(s1: *mut Char, s2: *Char) -> *mut Char
  function memset(s: *mut Void, c: Int, n: Uintn) -> *mut Void
  function strerror(errnum: Int) -> *mut Char
  function strlen(s: *Char) -> Uintn
}

// errno.h
extern {
  data errno: Int32
}

