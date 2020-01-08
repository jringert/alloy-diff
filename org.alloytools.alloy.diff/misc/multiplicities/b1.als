module b1

sig Object{}

sig Branch {}

sig Bank{
  branches: some (Branch + Bank)
}

pred xxx {
	all b : Bank | #b.branches > 0
}

fact {Branch + Bank = Object}

run xxx for 4
