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
    fib(n: n-1) + fib(n: n-2)
  }
}

function main() -> Int32 {
  /*let i: Int32 = */ add(a: 1, b: 2);
//   libc::printf(c"%d\n", i);
//   let j: Int32 = fib(n: 5);
//   libc::printf(c"%d\n", j);
  0
}
