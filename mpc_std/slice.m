import opt::Option
import vec::Vec
import arr
import mem
import prog

struct Slice<ElementType>(base: *mut ElementType, length: Uintn)

function (!Slice) from_ptr<ElementType>(base: *mut ElementType, length: Uintn) -> Slice<ElementType> {
  Slice(base, length)
}

function (!Slice) from_vec<ElementType>(vec: *Vec<ElementType>) -> Slice<ElementType> {
  Slice((*vec).mem, (*vec).length)
}

function (!Slice) from_array<ArrayType, ElementType>(array: *ArrayType) -> Slice<ElementType> {
  Slice(&(*array)[0], arr::length(array))
}

function (slice: Slice<ElementType>) at<ElementType>(index: Uintn) -> *mut ElementType {
  if index >= slice.length {
    prog::panic(c"Tried to access slice out of bounds\n");
  }
  mem::ptr_off(slice.base, index)
}

function (slice: Slice<ElementType>) at_or_none<ElementType>(index: Uintn) -> Option<*mut ElementType> {
  if index < slice.length {
    Option::Some(mem::ptr_off(slice.base, index))
  } else {
    Option::None
  }
}

function (slice: Slice<ElementType>) range<ElementType>(begin: Uintn, end: Uintn) -> Slice<ElementType> {
  if begin > end || end > slice.length {
    prog::panic(c"Tried to access slice out of bounds\n");
  }
  Slice(mem::ptr_off(slice.base, begin), end - begin)
}
