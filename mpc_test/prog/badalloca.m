/*
 * The following program causes a stack overflow if allocas are
 * emitted in the wrong place for aggregate return temporaries
 */

struct MyStruct (a: Intn, b: Intn, c: Intn, d: Intn)

function make_my_struct() -> MyStruct {
  MyStruct(0, 1, 2, 3)
}

function main() -> Int32 {
  let mut i = 0;
  while i < 1000000 {
    make_my_struct();
    i += 1;
  }
  0
}
