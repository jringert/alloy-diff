module b2

sig Branch{}

sig BranchDummy{
  field : Branch
}

sig Bankv2{
  branches: one BranchDummy
}
