extern {
  function printf(fmt: *Int8, arg: Int32) -> Int32
}

function add<T>(a: T, b: T) -> T {
  a + b
}

function fib<T>(n: Uintn) -> T {
  if n == 0 {
    return 0
  };
  if n == 1 {
    return 1
  };
  fib(n: n-1) + fib(n: n-2)
}

function main() {
  let i: Int32 = add(a: 1, b: 2);
  let j: Int32 = fib(n: 5);
}
