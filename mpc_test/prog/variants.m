/*
STDOUT
0
1 1 2
END
*/

import libc

enum MyEnum (
  Unit,
  Struct (a: Int32, b: Int32)
)

function main() -> Int32 {
  let u = MyEnum::Unit;
  libc::printf(c"%d\n", *(&u as <*Int32>));

  let s = MyEnum::Struct(a: 1, b: 2);
  let p = &s as <*[3]Int32>;
  libc::printf(c"%d %d %d\n", (*p)[0], (*p)[1], (*p)[2]);

  0
}