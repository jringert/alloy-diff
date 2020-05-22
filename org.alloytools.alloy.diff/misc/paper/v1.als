sig Endpoint {}
abstract sig Request {
  to: set Endpoint
}
sig LoginRequest extends Request {
  from: one Endpoint
}

run {}
