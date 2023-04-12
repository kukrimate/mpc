import arr
import mem
import opt
import prog
import vec

struct Slice<ElementType>(base: *mut ElementType, length: Uintn)

function from_ptr<ElementType>(base: *mut ElementType, length: Uintn) -> Slice<ElementType> {
  Slice(base, length)
}

function from_vec<ElementType>(vec: *vec::Vec<ElementType>) -> Slice<ElementType> {
  Slice((*vec).mem, (*vec).length)
}

function from_array<ArrayType, ElementType>(array: *ArrayType) -> Slice<ElementType> {
  Slice(&(*array)[0], arr::length(array))
}

function at<ElementType>(slice: Slice<ElementType>, index: Uintn) -> *mut ElementType {
  if index >= slice.length {
    prog::panic(c"ElementTyperied to access slice out of bounds\n");
  }
  mem::ptr_off(slice.base, index)
}

function at_or_none<ElementType>(slice: Slice<ElementType>, index: Uintn) -> opt::Option<*mut ElementType> {
  if index < slice.length {
    opt::some(mem::ptr_off(slice.base, index))
  } else {
    opt::none()
  }
}

function range<ElementType>(slice: Slice<ElementType>, begin: Uintn, end: Uintn) -> Slice<ElementType> {
  if begin > end || end > slice.length {
    prog::panic(c"ElementTyperied to access slice out of bounds\n");
  }
  Slice(mem::ptr_off(slice.base, begin), end - begin)
}
