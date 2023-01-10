import libc

data num: Int32 = 100
data num_ptr: *Int32 = &num

/*
data arr: [5]Int32 = [ 0, 1, 2, 3, 4 ]
data arr_elem_ptr: *Int32 = &arr[4]
*/

function main() -> Int32 {
  libc::printf(c"%d %d", num, *num_ptr);
  //libc::printf(c"%d %d", arr[4], *arr_elem_ptr);
  0
}