/*
Test the use of conditionals in both value and jumping code contexts
STDOUT
true
true
1
true
false
0
false
0
false
0
true
1
true
1
false
true
1
false
false
0
true
0
false
1
true
true
true
true
false
false
false
false
false
false
true
true
true
true
false
true
true
false
false
false
true
false
false
true
END
*/

import libc

function t() -> Bool {
  libc::printf(c"true\n");
  true
}

function f() -> Bool {
  libc::printf(c"false\n");
  false
}

function main() -> Int32 {
  libc::printf(c"%hhu\n", t() && t());
  libc::printf(c"%hhu\n", t() && f());
  libc::printf(c"%hhu\n", f() && t());
  libc::printf(c"%hhu\n", f() && f());
  libc::printf(c"%hhu\n", t() || t());
  libc::printf(c"%hhu\n", t() || f());
  libc::printf(c"%hhu\n", f() || t());
  libc::printf(c"%hhu\n", f() || f());
  libc::printf(c"%hhu\n", !t());
  libc::printf(c"%hhu\n", !f());
  if t() && t() { t() } else { f() }
  if t() && f() { t() } else { f() }
  if f() && t() { t() } else { f() }
  if f() && f() { t() } else { f() }
  if t() || t() { t() } else { f() }
  if t() || f() { t() } else { f() }
  if f() || t() { t() } else { f() }
  if f() || f() { t() } else { f() }
  if !t() { t() } else { f() }
  if !f() { t() } else { f() }
  0
}