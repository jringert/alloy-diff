sig Endpoint {}
sig LoginRequest {
  to: one Endpoint,
  from: one Endpoint
}
fact {
  from in LoginRequest lone -> one Endpoint
}

run {}
