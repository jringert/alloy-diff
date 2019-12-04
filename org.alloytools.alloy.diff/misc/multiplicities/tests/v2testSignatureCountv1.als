module b2

sig Bankv1{
  branches: some (common + Bankv1)
} {
  no branches
}

sig common{}