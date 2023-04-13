/*
STDOUT
A
0
B
1
C
2
D(1.000000)
3
END
*/

import libc

enum MyEnum (
  A,
  B,
  C,
  D(dbl: Double)
)

function main() -> Int32 {
  let a = [
    MyEnum::A,
    MyEnum::B,
    MyEnum::C,
    MyEnum::D(dbl: 1.0)
  ];

  let mut i = 0;
  while i < 4 {
    let val = match a[i] {
      A => { libc::printf(c"A\n"); 0 },
      B => { libc::printf(c"B\n"); 1 },
      C => { libc::printf(c"C\n"); 2 },
      D(dbl) => { libc::printf(c"D(%f)\n", dbl); 3 }
    };
    libc::printf(c"%d\n", val);
    i += 1;
  }

  0
}
