import libc

enum Option<T>(
  Some (val: T),
  None1,
  None2
)

function yield_unit() {}

function main() -> Int32 {
  match Option::None2 {
    s: Some => s.val,
    None1   => yield_unit(),
    None2   => ()
  }
  0
}
