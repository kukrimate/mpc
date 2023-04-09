/*
 * Verify that definition re-ordering works as expected
 */

union Foo (
  b: Bar
)

struct Bar (
  i: Int32
)

function main() -> Int32 {
  let a = Foo(Bar(1));
  0
}
