import libc

struct Foo (i: Intn, j: Intn)

function main() {
  let foo = Foo(1, 2);
  libc::printf(c"%ld %ld\n", foo.i, foo.j);
}
