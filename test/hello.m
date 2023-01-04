extern {
  function printf(str: *Uint8) -> Int32
}

function main() {
  printf(str: &"Hello World!\n"[0]);
}
