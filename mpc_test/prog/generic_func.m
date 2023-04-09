/*STDOUT
3
5
END
*/

import libc

function add<T>(a: T, b: Int32) -> Int32 {
  a + b
}

function fib<T>(n: Uintn) -> T {
  if n == 0 {
    0
  } else if n == 1 {
    1
  } else {
    fib(n - 1) + fib(n - 2)
  }
}

function main() -> Int32 {
  libc::printf(c"%d\n", add::<Int32>(a: 1, b: 2));
  libc::printf(c"%d\n", fib::<Int32>(n: 5));
  0
}
