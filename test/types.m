struct T1 (i: Intn, j: Intn, k: Uint32)

union T2 (i: Int32, f: Float, d: Double)

enum T3 (
  E1,
  E1 (v: T1),
  E3 (v: T2)
)

extern {
  data t1: T1
  data t2: T2
  data t3: T3
}

data t1p: *Intn = &t1.i
