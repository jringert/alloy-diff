module b2

sig Branch{}

sig Branch2{
	field2 : Branch
}
sig Bankv2{
  branches: one Branch
}
