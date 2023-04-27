import mem

struct Box<T>(mem: *mut T)

function (!Box) new<T>(val: T) -> Box<T> {
  let mem: *mut T = mem::allocate();
  *mem = val;
  Box(val)
}
