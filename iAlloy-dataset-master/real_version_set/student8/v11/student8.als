sig List {
  header: set Node
}

sig Node {
  link: set Node,
  elem: set Int
}

fact {
  all n: Node | one l: List | n = l.header || n in l.header.^link 
}

// Correct.
fact CardinalityConstraints {
  all l:List | lone l.header
  all n:Node | lone n.link
  all n:Node | one n.elem
}

// Correct.
pred Loop(This: List) {
  no This.header || one n:This.header.*link | n in n.link
}

// Overconstraint.  Should allow no n.link
pred Sorted(This: List) {
  all n:Node | n.elem <= n.link.elem
}

pred RepOk(This: List) {
  Loop[This]
  Sorted[This]
}

// Correct.
pred Count(This: List, x: Int, result: Int) {
  RepOk[This]
  #{n:This.header.*link | x in n.elem} = result
}

abstract sig Boolean {}
one sig True, False extends Boolean {}

// Correct.
pred Contains(This: List, x: Int, result: Boolean) {
  RepOk[This]
  x in This.header.*link.elem => result = True else result = False
}
run Loop for 20
run Sorted for 18
run RepOk for 17
run Count for 17
run Contains for 17
