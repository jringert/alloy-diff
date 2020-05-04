sig List {
    header: set Node
}

sig Node {
    link: set Node,
    elem: set Int
}

// Correct
fact CardinalityConstraints {
    all l: List | lone l.header
    all n: Node | lone n.link
    all n: Node | one n.elem
}

// Correct
pred Loop(This: List) {
    no This.header || one n: This.header.*link | n in n.^link
}

// Overconstraint.  Should allow no n.link
pred Sorted(This: List) {
    // Fix: replace "n.elem <= n.link.elem" with "some n.link => n.elem <= n.link.elem".
    all n:This.header.*link | n.elem <= n.link.elem
}

pred RepOk(This: List) {
     Loop[This]
     Sorted[This]
}

// Underconstraint.  result should be number of n
pred Count(This: List, x: Int, result: Int) {
    RepOk[This]
    // Fix: delete "all n: This.header.*link.elem | x = n".
    all n: This.header.*link.elem | x = n
    // Fix: replace "result = #x" with "result = #{n: This.header.*link | n.elem = x}".
    result = #x
}

abstract sig Boolean {}
one sig True, False extends Boolean {}

// Overconstraint.  Should allow no l.header
pred Contains(This: List, x: Int, result: Boolean) {
    RepOk[This]
    // Fix: replace "(some n: This.header.*link | x in n.elem && result = True) || (all n: This.header.*link | x !in n.elem && result = False)" with "((some n: This.header.*link | x in n.elem) && result = True) || ((all n: This.header.*link | x !in n.elem) && result = False)".
    (some n: This.header.*link | x in n.elem && result = True) || (all n: This.header.*link | x !in n.elem && result = False)
}

run Loop for 20
run Sorted for 18
run RepOk for 17
run Count for 17
run Contains for 17
