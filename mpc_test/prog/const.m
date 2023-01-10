import libc

const I32_100: Int32 = 100
const I32_200: Int32 = 200
const ARR: [5]Int32 = [ 0, 1, 2, 3, 4 ]

function main() {
  libc::printf(c"%d\n", I32_100);
  libc::printf(c"%d\n", I32_200);
  libc::printf(c"%d\n", ARR[4]);
}
