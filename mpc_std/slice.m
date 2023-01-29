import arr
import mem
import prog
import vec

struct Slice<T>(base: *mut T, length: Uintn)

function from_vec<ElementType>(vec: *vec::Vec<ElementType>) -> Slice<ElementType> {
  Slice((*vec).mem, (*vec).length)
}

function from_array<ArrayType, ElementType>(array: *ArrayType) -> Slice<ElementType> {
  Slice(&(*array)[0], arr::length(array))
}

function at<T>(slice: Slice<T>, index: Uintn) -> *mut T {
  if index >= slice.length {
    prog::panic(c"Tried to access slice out of bounds\n");
  }
  mem::ptr_off(slice.base, index)
}

function range<T>(slice: Slice<T>, begin: Uintn, end: Uintn) -> Slice<T> {
  if begin > end || end > slice.length {
    prog::panic(c"Tried to access slice out of bounds\n");
  }
  Slice(mem::ptr_off(slice.base, begin), end - begin)
}
