module extends1

sig A{
  children : A
}

sig B extends A {}

sig C extends A {}

sig D extends B {}

run {}
