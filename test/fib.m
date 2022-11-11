extern {
  function atoi(str: *Int8) -> Int32
  function puts(str: *Uint8) -> Int32
  function printf(fmt: *Int8, arg: Int32) -> Int32
}

function fib(mut n: Int32) {
  let mut i: Int32 = 0;
  let mut j: Int32 = 1;

  while n > 0 {
    printf(fmt: &"%d "[0], arg: i);
    let tmp = i + j;
    i = j;
    j = tmp;
    n -= 1;
  }
}

function main(argc: Int32, argv: *[0]*Int8) {
  if argc < 2 {
    puts(str: &"Usage: fib N"[0]);
  } else {
    let cnt_str = (*argv)[1];
    fib(n: atoi(str: cnt_str));
  }
}
