abstract sig A {}
sig B {}
one sig C extends A {}
sig D extends A {}


run {} for 3 but exactly 3 A, 3 B
