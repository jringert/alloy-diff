module CSOS
open Declaration
some sig Channel extends Class{}{
attrSet = channelID
id=channelID
isAbstract = No
}
one sig channelID extends Integer{}
one sig EmailChannel extends Class{}{
attrSet = emailID
one parent
parent in Channel
isAbstract = No
id=channelID
}
lone sig emailID extends Integer{}
one sig SecEmailChannel extends Class{}{
attrSet = secEmailID
one parent
parent in EmailChannel
isAbstract = No
id=channelID
}
abstract sig secEmailID extends Integer{}
one sig smsProvider extends string{}
one sig telNo extends string{}
one sig Principal extends Class{}{
attrSet = principalID + principalName
isAbstract = No
no parent
}
some sig principalID extends Integer{}
one sig principalName extends string{}
abstract sig Person extends Class{}{
attrSet = role
one parent
parent in Principal
isAbstract = No
id=principalID
}
one sig role extends Integer{}
one sig Viewer extends Class{}{
attrSet = period
id=principalID
one parent
parent in Person
isAbstract = No
}
one sig period extends Integer{}
one sig Institution extends Class{}{
attrSet = InstitutionID
one parent
parent in Principal
isAbstract = No
id=principalID
}
abstract sig InstitutionID extends Integer{}
one sig PrincipalProxy extends Association{}{
src = Principal
dst = Channel
src_multiplicity = ONE
dst_multiplicity = MANY
}
lone sig Role extends Class{}{
attrSet = roleID
id=roleID
isAbstract = No
no parent
}
abstract sig roleID extends Integer{}
one sig PrincipalRole extends Association{}{
src = Principal
dst = Role
src_multiplicity = MANY
dst_multiplicity = MANY
}
abstract sig ProcessStateMachine extends Class{}{
attrSet = stateMachineID 
id=stateMachineID
isAbstract = No
no parent
}
one sig stateMachineID extends Integer{}
one sig ProcessStateMachineState extends Class{}{
attrSet = stateID + entryActionID + exitActionID
id=stateID
isAbstract = No
no parent
}
one sig stateID extends Integer{}
lone sig entryActionID extends Integer{}
one sig exitActionID extends Integer{}
abstract sig ProcessStateMachineAction extends Class{}{
attrSet = actionID + actionStateMachineID
id=actionID
isAbstract = No
no parent
}
one sig actionID extends Integer{}
some sig actionStateMachineID extends Integer{}
abstract sig ProcessStateMachineEvent extends Class{}{
attrSet = eventID 
id=eventID
isAbstract = No
no parent
}
one sig eventID extends Integer{}
one sig StateMachineEvents extends Association{}{
src = ProcessStateMachine
dst = ProcessStateMachineEvent
src_multiplicity = ONE
dst_multiplicity = MANY
}
one sig StateMachineTransitions extends Association{}{
src = ProcessStateMachine
dst = ProcessStateMachineTransition
}
one sig ProcessStateMachineTransition extends Class{}{
attrSet = transitionID + fromStateID + toStateID 
id=transitionID
isAbstract = No
no parent
parent in Channel
}
one sig transitionID extends Integer{}
one sig fromStateID extends Integer{}
one sig toStateID extends Integer{}
one sig ProcessStateMachineExecution extends Class{}{
attrSet = processStateMachineExecutionID + processStateMachineID + currentStateID 
id=processStateMachineExecutionID
isAbstract = No
no parent
isAbstract = No
}
lone sig processStateMachineExecutionID extends Integer{}
one sig processStateMachineID extends Integer{}
one sig currentStateID extends Integer{}
one sig ProcessQueryResponseAction extends Class{}{
attrSet = processQueryResponseActionID
one parent
parent in ProcessStateMachineAction
isAbstract = No
id=actionID
}
lone sig processQueryResponseActionID extends Integer{}
one sig ProcessQueryResponseExecution extends Class{}{
attrSet = processQueryResponseExecutionID
one parent
isAbstract = No
id=processStateMachineExecutionID
}
one sig processQueryResponseExecutionID extends Integer{}
pred show{}
run show for 51
