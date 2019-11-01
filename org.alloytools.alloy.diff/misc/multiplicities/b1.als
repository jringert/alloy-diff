module b1

abstract sig Branch {}

sig Bank{
  branches: lone Branch
}
