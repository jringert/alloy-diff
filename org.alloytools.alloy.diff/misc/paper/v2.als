sig Endpoint {}
abstract sig Request {
  to: set Endpoint
}
sig LoginRequest extends Request{
  from: one Endpoint,
}{
  #to = 1
}
fact {
  all r1, r2 : LoginRequest | 
    r1.from = r2.from implies r1 = r2
}

run {}
