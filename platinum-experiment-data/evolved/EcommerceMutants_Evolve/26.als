module ecommerce
open Declaration
one sig Customer extends Class{}{
attrSet = customerID+customerName
id=customerID
isAbstract = No
no parent
}
one sig customerID extends Integer{}
one sig customerName extends string{}
abstract sig Order extends Class{}{
attrSet = orderID+orderValue
id=orderID
isAbstract = No
no parent
}
abstract sig orderID extends Integer{}
one sig orderValue extends Integer{}
one sig ShippingCart extends Class{}{
attrSet = shippingCartID
id=shippingCartID
isAbstract = No
}
one sig shippingCartID extends Integer{}
abstract sig Item extends Class{}{
attrSet = ItemID+quantity
id=ItemID
isAbstract = No
no parent
}
some sig ItemID extends Integer{}
one sig quantity extends Integer{}
some sig CartItem extends Class{}{
attrSet = cartItemID
id=cartItemID
isAbstract = No
parent in Item
}
one sig cartItemID extends Integer{}
one sig ShippingCartItemAssociation extends Association{}{
src = ShippingCart
dst = Item
src_multiplicity = ONE
dst_multiplicity = MANY
}
one sig status extends Integer{}
one sig orderItemID extends Integer{}
one sig OrderItemAssociation extends Association{}{
src = Order
dst = Item
src_multiplicity = ONE
dst_multiplicity = MANY
}
one sig Category extends Class{}{
attrSet = categoryID+categoryName
id=categoryID
isAbstract = No
no parent
}
one sig categoryID extends Integer{}
abstract sig categoryName extends string{}
one sig ProductCategoryAssociation extends Association{}{
src = Product
dst = Category
src_multiplicity = MANY
dst_multiplicity = MANY
}
some sig Catalog extends Class{}{
attrSet = CatalogID
id=CatalogID
isAbstract = No
no parent
}
abstract sig CatalogID extends Integer{}
one sig ProductItemAssociation extends Association{}{
src = Product
dst = Item
src_multiplicity = MANY
dst_multiplicity = MANY
}
one sig Product extends Class{}{
attrSet = productID+productName+description+price
id=productID
isAbstract = No
no parent
}
one sig productName extends string{}
one sig description extends string{}
one sig price extends Real{}
one sig PhysicalProduct extends Class{}{
attrSet = weight+availability
id=productID
isAbstract = No
parent in Product
}
one sig weight extends Real{}
abstract sig availability extends Bool{}
one sig Service extends Class{}{
attrSet = schedule
id=productID
isAbstract = No
parent in Product
}
one sig schedule extends string{}
one sig Asset extends Class{}{
attrSet = assetID+assetName+fileURI
id = assetID
isAbstract = No
no parent
}
one sig assetID extends Integer{}
one sig assetName extends string{}
one sig fileURI extends string{}
one sig Media extends Class{}{
attrSet = mediaType
id = assetID
isAbstract = No
parent in Asset
}
lone sig mediaType extends Integer{}
one sig Documents extends Class{}{
attrSet = excerpt
id = assetID
isAbstract = No
parent in Asset
}
one sig excerpt extends string{}
one sig ElectronicProduct extends Class{}{
id=productID
isAbstract = No
}
one sig productID extends Integer{}
one sig OrderItem extends Class{}{
attrSet = orderItemID+status
id=orderItemID
isAbstract = No
parent in Item
}
one sig CustomerShippingCartAssociation extends Association{}{
src = Customer
dst = ShippingCart
src_multiplicity = ONE
dst_multiplicity = MANY
}
pred show{}
run show for 50
