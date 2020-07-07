sig Node {
  left : lone Node
}
one sig A extends Node {
  a : set Node
}
one sig B {
  a : set Node
}
lone sig C {
  a : set Node
}
fact acyclic {no n: Node | n in n.^left}
fact succ {all n: Node | lone n.^left}

run {} for 10
