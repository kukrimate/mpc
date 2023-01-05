extern {
  function atoi(str: *Int8) -> Int32
  function memcpy(dest: *Uint8, src: *Uint8, len: Uintn) -> *Uint8
  function memset(dest: *Uint8, src: *Uint8, len: Uintn) -> *Uint8
  function printf(fmt: *Int8, ...) -> Int32
  function puts(str: *Uint8) -> Int32
  data errno: Int32
}
