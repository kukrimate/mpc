/*
STDOUT
4621819117588971520 10.000000
4621819117588971520 10.000000
4621819117588971520 10.000000
4621819117588971520 10.000000
END
*/

import libc

union Foo (i: Int64, d: Double)

data u1: Foo = Foo(i: 4621819117588971520)
data u1_p1: *Int64 = &u1.i
data u1_p2: *Double = &u1.d

data u2: Foo = Foo(d: 10.0)
data u2_p1: *Int64 = &u2.i
data u2_p2: *Double = &u2.d

union Foo2 (a: Int64, b: [16]Uint8)

data u3: Foo2 = Foo2(b: [ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15 ])

function main() -> Int32 {
  // Data section
  libc::printf(c"%ld %lf\n", *u1_p1, *u1_p2);
  libc::printf(c"%ld %lf\n", *u2_p1, *u2_p2);
  let ptr = &u3;
  // Union locals
  let a = Foo(i: 4621819117588971520);
  libc::printf(c"%ld %lf\n", a.i, a.d);
  let b = Foo(d: 10.0);
  libc::printf(c"%ld %lf\n", b.i, b.d);
  0
}
