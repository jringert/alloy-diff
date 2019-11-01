module b

sig Branch {}

sig Bank{
  branches: set Branch
}

pred b1 {
  all b : Bank | #b.branches <=1
}

pred b2 {
  all b : Bank | #b.branches =1
}

run {b1 and not b2} for 200
