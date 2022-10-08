struct T1 (i: Intn, j: Intn, k: Uint32)

union T2 (i: Int32, f: Float)

enum T3 (
  E1,
  E1 (v: T1),
  E3 (v: T2)
)

