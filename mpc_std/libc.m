extern {
  function atoi(str: *Int8) -> Int32

  // stdlib.h
  function abort()
  function rand() -> Int32
  function srand(seed: Uint32)

  // string.h
  function memcpy(dest: *Uint8, src: *Uint8, len: Uintn) -> *Uint8
  function memset(dest: *Uint8, c: Int32, len: Uintn) -> *Uint8
  function memmove(dest: *Uint8, src: *Uint8, len: Uintn) -> *Uint8

  // errno.h
  data errno: Int32

  // stdio.h
  data stdin: *mut libc::FILE
  data stdout: *mut libc::FILE
  data stderr: *mut libc::FILE

  function printf(fmt: *Int8, ...) -> Int32
  function fprintf(stream: *mut libc::FILE, fmt: *Int8, ...) -> Int32
  function puts(str: *Uint8) -> Int32
}

struct FILE()
