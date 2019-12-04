module bankOneBranch

sig Branch {}

sig Bank{
  branches: some Branch
}