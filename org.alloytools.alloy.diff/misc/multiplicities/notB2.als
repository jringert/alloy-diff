module b

sig Branch {}

sig Bank{
  branches: one Branch
}

pred b2 {
  branches in Bank set -> one Branch
  //all b : Bank | #b.branches =1
}

run {not b2} for 10
