extern {
  function printf(fmt: *Int8, arg: Int32) -> Int32
}

function add<T>(a: T, b: T) -> T {
  a + b
}

function main() {
  printf(fmt: &"%d"[0], arg: add(a: 1, b: 2));
}
