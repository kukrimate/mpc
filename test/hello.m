extern {
  function printf(fmt: *Uint8, ...) -> Int32
}

function main() {
  printf(c"Hello World!\n");
}
