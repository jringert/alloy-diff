module bank

sig Bank{
  branches: set Bank
}

sig ATM extends Bank {
  owner : one Bank,
  others : branches - owner
}

run {}