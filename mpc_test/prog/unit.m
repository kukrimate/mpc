/* Test local allocation and parameter passing for unit types
STDOUT
OK
END*/

import libc

// Equivalent C code will have signature:
// void print(const char *str);

function print(unit1: (), unit2: (), str: *Int8) -> () {
  libc::puts(str);
}

function main() -> Int32 {
  // Allocate unit typed local
  let unit = ();
  // Pass to function
  print((), (), c"OK");
  0
}
