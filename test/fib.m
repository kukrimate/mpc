const n: Int32 = 100

function fib(n: Int32) {
  let mut i: Int32 = 0;
  let mut j: Int32 = 1;

  loop {
    let tmp = i + j;
    i = j;
    j = tmp;
  }
}

function main() {
  fib(n: n)
}
