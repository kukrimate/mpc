/*
STDOUT
5
6
END
*/

import libc

struct MyStruct(val: Int32)

function foo() -> MyStruct {
  loop { return MyStruct(5) }
  // This point is unreachable, yet the entire loop should type check as
  // non-existent MyStruct value
}

function main() -> Int32 {
  let my_foo = foo();
  libc::printf(c"%d\n", my_foo.val);
  let val2 = loop {
    break 6
  };
  libc::printf(c"%d\n", val2);
  loop { break 0 }
}
