/*
STDOUT
1
10.000000
END
*/

import libc

union Foo (i: Int64, d: Double)

function main() -> Int32 {
  let a = Foo(i: 1);
  libc::printf(c"%ld\n", a.i);
  let b = Foo(d: 10.0);
  libc::printf(c"%lf\n", b.d);
  0
}
