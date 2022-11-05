data n: Int32 = 100

function fib(mut n: Int32) {
  let mut i: Int32 = 0;
  let mut j: Int32 = 1;

  while n > 0 {
    let tmp = i + j;
    i = j;
    j = tmp;
    n -= 1;
  }
}

function main() {
  fib(n: n);
}
