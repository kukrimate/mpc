/*
STDOUT
A
0
B
1
C
2
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
    let val = match a[i] {
      A => { libc::printf(c"A\n"); 0 },
      B => { libc::printf(c"B\n"); 1 },
      C => { libc::printf(c"C\n"); 2 }
    };
    libc::printf(c"%d\n", val);
    i += 1;
  }
  0
}
