enum State { On, Off }

sig A {
  state : one State
}

run {one A}
