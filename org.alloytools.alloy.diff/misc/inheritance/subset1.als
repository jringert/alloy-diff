sig A {
  a : some A
}

sig C {
  c : some C
}

sig B in A + C {
  b : some A
}

run {no B.c}
