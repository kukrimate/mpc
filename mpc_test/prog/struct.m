/*
STDOUT
1 2
END
*/

import libc

struct Foo (i: Intn, j: Intn)

function main() -> Int32 {
  let foo = Foo(1, 2);
  libc::printf(c"%ld %ld\n", foo.i, foo.j);
  0
}
