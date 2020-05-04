sig A {
  next : one A
}

run {some x1, x2 : A | x1.next = x2 }
