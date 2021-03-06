module decider
open Declaration
some sig NameSpace extends Class{}{
attrSet = namespaceID+namespaceName
id=namespaceID
isAbstract = No
no parent
}
some sig namespaceID extends Integer{}
some sig namespaceName extends string{}
one sig Variable extends Class{}{
//attrSet = variableID+variableName
id=variableID
isAbstract = No
no parent
}
one sig variableID extends Integer{}
one sig variableName extends string{}
some sig Relationship extends Class{}{
attrSet = relationshipID+relationshipName
id=relationshipID
isAbstract = No
}
some sig relationshipID extends Integer{}
one sig relationshipName extends string{}
one sig varAssociation extends Association{}{
src = Variable
dst = Relationship
//src_multiplicity = ONE
//dst_multiplicity = MANY
}
some sig Role extends Class{}{
attrSet = roleID //+roleName
id=roleID
no parent
}
some sig roleID extends Integer{}
abstract sig DecisionSpace extends Class{}{
attrSet = decisionSpaceName
id=namespaceID
isAbstract = No
one parent
parent in NameSpace
}
one sig decisionSpaceName extends string{}
some sig Participant extends Class{}{
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
some sig descisionSpaceVariablesAssociation extends Association{}{
//src = DecisionSpace
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
lone sig password extends string{}
one sig Viewer extends Class{}{
attrSet = period
id=participantID
one parent
isAbstract = No
}
lone sig period extends Integer{}

one sig Developer extends Class{}{
attrSet = department
//id=participantID
one parent
//parent in User
//isAbstract = No
}
one sig department extends Integer{}
pred Decider{}
run Decider for 30
