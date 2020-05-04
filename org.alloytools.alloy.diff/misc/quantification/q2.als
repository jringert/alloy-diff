sig A {
  next : one A
}

run {some x1 : set A | all a : x1| a.next in x1 }
