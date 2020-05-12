module wordpress
open Declaration
one sig CommentMeta extends Class{}{
attrSet = commentID+ commentMetaValue
id=commentID
isAbstract = No
no parent
}
one sig commentID extends Integer{}
one sig commentMetaValue extends string{}
one sig Comments extends Class{}{
attrSet=commentContent
id=commentID
isAbstract = No
one parent
parent in CommentMeta
}
lone sig commentContent extends string{}
lone sig CommentPostAssociation extends Association{}{
src=Posts//Commentmeta//
dst=Comments //PostMeta
src_multiplicity = ONE
dst_multiplicity = MANY
}
one sig CommentUserAssociation extends Association{}{
src=Users
dst=Comments
src_multiplicity = ONE
dst_multiplicity = MANY
}
one sig Links extends Class{}{
attrSet=linkID//+linkUrl
id=linkID
isAbstract = No
no parent
}
one sig linkID extends Integer{}
lone sig PostMeta extends Class{}{
attrSet=postID//+postMetaValue
id=postID
isAbstract = No
no parent
}
one sig postID extends Integer{}
one sig Posts extends Class{}{
attrSet=postContent
id=postID
isAbstract = No
one parent
parent in PostMeta
}
lone sig postContent extends string{}
one sig Pages extends Class{}{
attrSet=pageTitle
id=postID
isAbstract = No
one parent
parent in Posts
}
one sig UserMeta extends Class{}{
attrSet=userID//+userMetaValue
id=userID
isAbstract = No
no parent
}
one sig userID extends Integer{}
one sig Users extends Class{}{
attrSet=userName
id=userID
isAbstract = No
one parent
parent in UserMeta
}
one sig userName extends string{}
one sig Terms extends Class{}{
attrSet=termID+termName
id=termID
isAbstract = No
no parent
}
one sig termID extends Integer{}
lone sig termName extends Integer{}
some sig TermPostsAssociation extends Association{}{
src = Terms
dst = Posts //PostMeta
src_multiplicity = MANY
dst_multiplicity = ONE
}
abstract sig TermLinksAssociation extends Association{}{
src = Terms
dst = Links
src_multiplicity = ONE
dst_multiplicity = MANY
}
abstract sig Category extends Class{}{
attrSet=categoryName
id=termID
isAbstract = No
one parent
parent in Terms
}
one sig categoryName extends string{}
lone sig PostCategory extends Class{}{
attrSet=postCategoryName
id=termID
isAbstract = No
one parent
parent in Category
}
lone sig postCategoryName extends string{}
lone sig LinkCategory extends Class{}{
attrSet=linkCategoryName
id=termID
isAbstract = No
one parent
parent in Category
}
lone sig linkCategoryName extends string{}
lone sig pageTitle extends string{}
pred Wordpress{}
run Wordpress for 32
