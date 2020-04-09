sig A {
  x : String
}

sig B {
  x : String
}

run {A.x="Jan" and B.x="Jan" and #String = 1} for 3
