sig A {
  b1 : set A,
  b2 : set A
}

// the two different facts need to be aware of whick As are identified as Bs. Because both have to apply to the same As.

fact flattened {

  some B : set A | 
    (all b : B | one b.b1) and (all b : B | one b.b2) and
    (all a : A | a !in B implies (no a.b1 and no a.b2))

}




run {one A}
