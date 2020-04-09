sig A {
  a : some A
}

sig C {
  c : some C
}

sig B in A + C {
  b : some A
}

sig D in B {
  d : some C
}

run {no B}
