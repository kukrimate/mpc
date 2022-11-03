data n: Int32 = 100
data np: *Int32 = &n

extern {
  data na: [5]Int32
}

data nap: *Int32 = &na[100]
