module b

sig Branch {}

sig Bank{
  branches: lone Branch
}

pred b1 {
}

pred b2 {
  branches in Bank set -> one Branch
  //all b : Bank | #b.branches =1
}

run {b1 and not b2} for 200
