module flattened_with_subsetSig

sig A {children : As}

sig B {children : As}

sig C {}

sig D {}

sig As in A + B + C+ D{}
sig Bs in B + D {}
sig Cs in C {}
sig Ds in D {}

run {}
