data foo: Intn = 5

function fib(n: Int32) {
  let i: Int32 = 0;
  let j: Int32 = 1;

  loop {
    let tmp = i + j;
    i = j;
    j = tmp;
  }
}

function main() {
  fib(n: 100)
}
