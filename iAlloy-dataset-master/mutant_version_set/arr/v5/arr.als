module unknown
//JOR//open util/integer [] as integer
sig Element {}
one sig Array {
i2e: (Int->Element),
length: (set Int)
}
pred NoConflict[] {
(one idx: (one ((Array.i2e).Element)) {
(lone (idx.(Array.i2e)))
})
}

fact Reachable {
(Element = (Int.(Array.i2e)))
}
fact InBound {
((some idx: (one ((Array.i2e).Element)) {
((idx = 0) && (idx < (Array.length)))
}) && ((Array.length) >= 0))
}

run NoConflict for 400
