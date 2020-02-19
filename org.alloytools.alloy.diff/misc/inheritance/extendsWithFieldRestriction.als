sig A {
  x : some A
}

sig B extends A {}

sig C {
  x : one A
}

fact {
  no (A<:x).A
}

run {}
