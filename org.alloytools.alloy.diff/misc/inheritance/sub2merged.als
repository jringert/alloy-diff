sig A {
  a : some A
}

sig Ab in A {
  b : some A
}

sig Ac in A {
  c : some A
}

sig Ad in A {
  d : some (Ab + Ac)
}

pred v1 {
  A.d in Ab
  all a : A | a in Ac iff a in Ad
}

pred v2 {
  all a : A | a in Ab iff a in Ac
}

run { v1 and not v2 }
