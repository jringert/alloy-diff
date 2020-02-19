module flattened_with_subsetSig

sig A {children : A + B + C+ D}

sig B {children : A + B + C+ D}

sig C {}

sig D {}

run {}
