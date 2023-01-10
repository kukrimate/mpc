/*
STDOUT
100 100
4 4
0
END
*/

import libc

data num: Int32 = 100
data num_ptr: *Int32 = &num

data arr: [5]Int32 = [ 0, 1, 2, 3, 4 ]
data arr_elem_ptr: *Int32 = &arr[4]

data arr_elem: Int32 = [ 0, 1 ][0]

function main() -> Int32 {
  libc::printf(c"%d %d\n", num, *num_ptr);
  libc::printf(c"%d %d\n", arr[4], *arr_elem_ptr);
  libc::printf(c"%d\n", arr_elem);
  0
}