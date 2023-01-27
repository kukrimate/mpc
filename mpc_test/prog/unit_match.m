import libc

enum Option<T>(
  Some (val: T),
  None
)

function main() -> Int32 {
  match Option::None {
    s: Some => s.val,
    None    => ()
  }
  0
}
