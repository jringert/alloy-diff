enum State { On, Off }

sig A {
  state : one State
} {
  state = On
}

run {one A}
