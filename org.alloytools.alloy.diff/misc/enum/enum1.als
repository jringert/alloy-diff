enum State { On, Off }

sig A {
  state : one State
}

fact {
  A.state = On
}

run {one A}
