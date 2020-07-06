sig Node {
  left : lone Node
}
fact acyclic {no n: Node | n in n.^left}
fact succ {all n: Node | lone n.^left}

run {} for 10
