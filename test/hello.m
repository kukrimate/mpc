extern {
  function puts(str: *Uint8) -> Int32
}

function main() {
  puts(str: &"Hello World!"[0]);
}
