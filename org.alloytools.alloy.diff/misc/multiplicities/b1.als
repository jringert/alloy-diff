module b2

sig Branch {}

sig Bank{
  branches: some (Branch + Bank)
} {
  no branches
}
