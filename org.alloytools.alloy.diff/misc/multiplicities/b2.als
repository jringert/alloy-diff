module b2

sig Branch {}

sig Bank{
  branches: one Branch
}
