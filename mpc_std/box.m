import mem

struct Box<T>(mem: *mut T)

function new<T>(val: T) -> Box<T> {
  let mem: *mut T = mem::allocate();
  *mem = val;
  Box(val)
}
