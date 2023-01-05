extern {
  function atoi(str: *Int8) -> Int32
  function printf(fmt: *Int8, ...) -> Int32
}

function fib(mut n: Int32) {
  let mut i: Int32 = 0;
  let mut j: Int32 = 1;

  while n > 0 {
    printf(c"%d\n", i);
    let tmp = i + j;
    i = j;
    j = tmp;
    n -= 1;
  }
}

function main(argc: Int32, argv: *[0]*Int8) {
  if argc < 2 {
    printf(c"Usage: fib N\n");
  } else {
    fib(atoi((*argv)[1]));
  }
}
