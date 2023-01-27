/*STDOUT
1 1.000000
END
*/

import libc

struct Pair <A, B> (a: A, b: B)

function main() -> Int32 {
  let p = Pair(1, 1.0);
  libc::printf(c"%d %f\n", p.a, p.b as <Double>);
  0
}
