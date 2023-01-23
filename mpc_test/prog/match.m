/*
STDOUT
A
B
C
END
*/

import libc

enum MyEnum (
  A,
  B,
  C
)

function main() -> Int32 {
  let a = [ MyEnum::A, MyEnum::B, MyEnum::C ];
  let mut i = 0;
  while i < 3 {
    match a[i] {
      A => libc::printf(c"A\n"),
      B => libc::printf(c"B\n"),
      C => libc::printf(c"C\n")
    }
    i += 1;
  }
  0
}
