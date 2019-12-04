module bankOneBranch

sig Branch {}

sig Bank{
  branches: one Branch
}

fact {
	all b : Bank | one b.branches
}