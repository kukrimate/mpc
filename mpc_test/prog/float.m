/*
STDOUT
11.100000
END
*/

import libc

function main() -> Int32 {
  let mut f: Double = 0.1;
  f += 0.1e2;
  f += 0.1e1;
  libc::printf(c"%lf\n", f);
  0
}
