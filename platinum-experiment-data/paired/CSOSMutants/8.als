module CSOS
open Declaration
one sig Channel extends Class{}{
attrSet = channelID
id=channelID
isAbstract = No
no parent
}
one sig channelID extends Integer{}
one sig EmailChannel extends Class{}{
attrSet = emailID
one parent
parent in Channel
isAbstract = No
id=channelID
}
one sig emailID extends Integer{}
one sig SecEmailChannel extends Class{}{
attrSet = secEmailID
one parent
parent in EmailChannel
isAbstract = No
id=channelID
}
one sig secEmailID extends Integer{}
one sig SMSChannel extends Class{}{
one parent
parent in Channel
isAbstract = No
id=channelID
}
one sig smsProvider extends string{}
abstract one sig telNo extends string{}
one sig Principal extends Class{}{
attrSet = principalID + principalName
id=principalID
isAbstract = No
}
one sig principalID extends Integer{}
lone sig principalName extends string{}
one sig Person extends Class{}{
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
one sig InstitutionID extends Integer{}
one sig PrincipalProxy extends Association{}{
src = Principal
dst = Channel
src_multiplicity = ONE
dst_multiplicity = MANY
}
one sig Role extends Class{}{
attrSet = roleID
id=roleID
isAbstract = No
no parent
}
one sig roleID extends Integer{}
one sig PrincipalRole extends Association{}{
src = Principal
dst = Role
src_multiplicity = MANY
}
one sig ProcessStateMachine extends Class{}{
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
one sig entryActionID extends Integer{}
one sig exitActionID extends Integer{}
one sig ProcessStateMachineAction extends Class{}{
attrSet = actionID + actionStateMachineID
id=actionID
isAbstract = No
no parent
}
one sig actionID extends Integer{}
one sig actionStateMachineID extends Integer{}
one sig MachineStates extends Association{}{
src = ProcessStateMachine
dst = ProcessStateMachineState
src_multiplicity = ONE
dst_multiplicity = MANY
}
one sig ProcessStateMachineEvent extends Class{}{
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
src_multiplicity = ONE
dst_multiplicity = MANY
}
one sig ProcessStateMachineTransition extends Class{}{
attrSet = transitionID + fromStateID + toStateID
id=transitionID
isAbstract = No
no parent
}
one sig transitionID extends Integer{}
one sig fromStateID extends Integer{}
one sig toStateID extends Integer{}
one sig ProcessStateMachineExecution extends Class{}{
attrSet = processStateMachineExecutionID + processStateMachineID + currentStateID
id=processStateMachineExecutionID
isAbstract = No
no parent
}
one sig processStateMachineExecutionID extends Integer{}
abstract one sig processStateMachineID extends Integer{}
one sig currentStateID extends Integer{}
abstract one sig ProcessQueryResponse extends Class{}{
attrSet = processQueryResponseID
one parent
parent in ProcessStateMachine
isAbstract = No
id=stateMachineID
}
one sig processQueryResponseID extends Integer{}
one sig processQueryResponseActionID extends Integer{}
one sig ProcessQueryResponseExecution extends Class{}{
attrSet = processQueryResponseExecutionID
one parent
parent in ProcessStateMachineExecution
isAbstract = No
id=processStateMachineExecutionID
}
one sig processQueryResponseExecutionID extends Integer{}
pred show{}
run show for 54
