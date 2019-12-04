module b2

sig Object{}

sig Branch extends Object {}

sig Bank{
  branches: some (Branch + Bank)
}

pred xxx {
	no Object
}

fact {Branch + Bank = Object}

run xxx for 4