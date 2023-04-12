/*
STDOUT
1 2
END
*/

import libc

struct Foo (i: Intn, j: Intn)

function (f: *Foo) getI() -> Intn {
  (*f).i
}

function (f: Foo) getJ() -> Intn {
  f.j
}

function main() -> Int32 {
  let foo = Foo(1, 2);
  libc::printf(c"%ld %ld\n", (&foo).getI(), foo.getJ());
  0
}
