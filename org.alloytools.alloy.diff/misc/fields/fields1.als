module bank

sig Bank{
  branches: set Bank,
  owner : Bank - branches
}

run {}