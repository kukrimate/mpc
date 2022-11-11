extern {
  function printf(fmt: *Int8, arg: Double) -> Int32
}

function main() {
  let mut f: Double = 0.1;
  f += 0.1e2;
  f += 0.1e1;
  printf(fmt: &"%lf"[0], arg: f);
}
