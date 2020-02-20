module extends1_flattened_direct

sig A {children : A + B + C+ D}

sig B {children : A + B + C+ D}

sig C {children : A + B + C+ D}

sig D {children : A + B + C+ D}

run {}
