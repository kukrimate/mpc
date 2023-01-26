/*
STDOUT
0 1
1 2
END
*/

import libc

const TUP: (a: Int32, b: Int32) = (a: 0, b: 1)

function main() -> Int32 {
  libc::printf(c"%d %d\n", TUP.a, TUP.b);
  let tup = (a: 1, b: 2);
  libc::printf(c"%d %d\n", tup.a, tup.b);
  0
}
