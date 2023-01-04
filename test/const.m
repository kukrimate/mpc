const I32_100: Int32 = 100
const I32_200: Int32 = 200

extern {
  function printf(fmt: *Int8, arg: Int32) -> Int32
}

function main(argc: Int32, argv: *[0]*Int8) {
  printf(fmt: &"%d "[0], arg: I32_100);
  printf(fmt: &"%d "[0], arg: I32_200);
}
