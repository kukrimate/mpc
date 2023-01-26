import libc

function main() -> Int32 {
  {
    let p: *() = main as <*()>;
    if main != p as <Function() -> Int32> {
      return 1
    }
  }

  {
    let i: Int8 = 5;
    let p1: *Int8 = &i;
    if i != *p1 {
      return 1
    }
  }

  {
    let mut j: Int8 = 8;
    let p2: *mut Int8 = &j;
    *p2 = 8;
    if j != *p2 {
      return 1
    }
  }

  {
    let p3: *Int32 = nil;
    if p3 == nil {
       0
    } else {
      1
    }
  }
}
