module b2

sig Branchv1 {}

sig Bankv1{
  branches: some (Branchv1 + Bankv1)
} {
  no branches
}
