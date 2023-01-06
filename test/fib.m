import libc

function fib(mut n: Int32) {
  let mut i: Int32 = 0;
  let mut j: Int32 = 1;

  while n > 0 {
    libc::printf(c"%d\n", i);
    let tmp = i + j;
    i = j;
    j = tmp;
    n -= 1;
  }
}

function main(argc: Int32, argv: *[0]*Int8) {
  if argc < 2 {
    libc::printf(c"Usage: fib N\n");
  } else {
    let n = libc::atoi((*argv)[1]);
    fib(n);
  }
}
