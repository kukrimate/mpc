/*
STDOUT
A
any
any
any
any
any
END
*/

import arr
import libc

enum E ( A, B, C, D, E, F )

function main() -> Int32 {
  let vals = [ E::A, E::B, E::C, E::D, E::E, E::F ];
  let mut i = 0;
  while i < arr::length(&vals) {
    match vals[i] {
      A => libc::printf(c"A\n"),
      * => libc::printf(c"any\n")
    }
    i += 1;
  }
  0
}
