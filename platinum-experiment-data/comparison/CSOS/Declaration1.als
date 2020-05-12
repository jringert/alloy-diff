module Declaration

abstract sig needHandle{}

abstract sig Class extends Attribute{
	attrSet: set Attribute,
	id: set Attribute,
	parent: lone Class,
	isAbstract: Bool
}

abstract sig Attribute extends needHandle{
//	type:Type+Class
}

abstract sig Type extends Attribute{}
sig Integer extends Type{}
sig Real extends Type{}
sig string extends Type{}
sig Bool extends Type{}
one sig Yes extends Bool{}
one sig No extends Bool{}
sig DType extends Type{}
sig Longblob extends Type{}
sig Time extends Type{}

abstract sig Multiplicity_State{}
one sig ONE extends Multiplicity_State{}
one sig MANY extends Multiplicity_State{}

abstract sig Association extends needHandle{
	src: one Class,
	dst: one Class,
	src_multiplicity: one Multiplicity_State,
	dst_multiplicity:one Multiplicity_State
}
/*
pred Declaration{}
run Declaration for 10*/
