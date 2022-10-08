extern {
  function puts(str: *Uint8) -> Int32
  function memcpy(dest: *Uint8, src: *Uint8, len: Uintn) -> *Uint8
  function memset(dest: *Uint8, src: *Uint8, len: Uintn) -> *Uint8
  data errno: Int32
}
