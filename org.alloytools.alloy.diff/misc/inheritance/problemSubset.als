sig A {

}

sig B in A {
  b1 : set A
  b2 : set A
}

// the two different facts need to be aware of whick As are identified as Bs. Because both have to apply to the same As.

fact oneB1 {
  all b : B | one b.b1
}

fact oneB2 {
  all b : B | one b.b2
}

run {one A and one B}
