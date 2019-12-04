module b2

sig Object{}

one sig Branch {}

fact {Branch + Bank = Branch}

sig Bank{
  branches: one Branch
}
