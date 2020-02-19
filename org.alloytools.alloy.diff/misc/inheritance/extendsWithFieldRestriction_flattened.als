sig A {
  x : some A
}

sig B {
  x : some A
}

sig C {
  x : one (A+B)
}

fact {
  no (A<:x + B<:x).(A+B)
}

run {}
