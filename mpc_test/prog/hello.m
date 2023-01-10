/*
STDOUT
Hello World!
END
*/

import libc

function main() -> Int32 {
  libc::printf(c"Hello World!\n");
  0
}
