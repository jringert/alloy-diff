module SinglyLinkedList
//JOR//open util/integer [] as integer
sig List {
header: (lone Node)
}
sig Node {
link: (lone Node)
}
pred Acyclic[l: List] {
((no (l.header)) || (some n: (one ((l.header).(*link))) {
(no (n.link))
}))
}



run Acyclic
