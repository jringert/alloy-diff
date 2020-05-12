module decider
open Declaration
some sig NameSpace extends Class{}{
attrSet = namespaceID+namespaceName
id=namespaceID
isAbstract = No
no parent
}
lone sig namespaceID extends Integer{}
lone sig namespaceName extends string{}
some sig Variable extends Class{}{
attrSet = variableID+variableName
id=variableID
isAbstract = No
no parent
}
one sig variableID extends Integer{}
abstract sig variableName extends string{}
lone sig Relationship extends Class{}{
attrSet = relationshipID+relationshipName
id=relationshipID
isAbstract = No
no parent
}
some sig relationshipID extends Integer{}
lone sig relationshipName extends string{}
one sig varAssociation extends Association{}{
src = Variable
dst = Relationship
src_multiplicity = ONE
dst_multiplicity = MANY
}
one sig Role extends Class{}{
attrSet = roleID //+roleName
id=roleID
no parent
}
abstract sig roleID extends Integer{}
lone sig DecisionSpace extends Class{}{
attrSet = decisionSpaceName
id=namespaceID
isAbstract = No
one parent
parent in NameSpace
}
one sig decisionSpaceName extends string{}
one sig Participant extends Class{}{
attrSet=participantID
id=participantID
isAbstract = No
no parent
}
one sig participantID extends Integer{}
one sig descisionSpaceParticipantsAssociation extends Association{}{
src = DecisionSpace
dst = Participant
src_multiplicity = MANY
dst_multiplicity = MANY
}
one sig descisionSpaceVariablesAssociation extends Association{}{
src = DecisionSpace
dst = Variable
src_multiplicity = ONE
dst_multiplicity = MANY
}
lone sig User extends Class{}{
attrSet = username+password
id=participantID
one parent
parent in Participant
isAbstract = No
}
one sig username extends string{}
one sig password extends string{}
lone sig Viewer extends Class{}{
attrSet = period
id=participantID
one parent
isAbstract = No
}
one sig period extends Integer{}
lone sig Developer extends Class{}{
attrSet = department
id=participantID
one parent
parent in User
isAbstract = No
}
lone sig department extends Integer{}
pred Decider{}
run Decider for 28
