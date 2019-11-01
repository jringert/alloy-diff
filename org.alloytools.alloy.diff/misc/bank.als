module bank

sig Branch {}

sig Bank{
  branches: set Branch
} {
  #branches = 1
}

fact {
  no Branch
}

pred a (X : set univ) {
  #X = 0
}
pred b {
  #Bank = 0
}

run {a[Branch] or b} for 7
