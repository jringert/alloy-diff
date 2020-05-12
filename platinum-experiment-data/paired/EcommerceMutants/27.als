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
one sig Order extends Class{}{
attrSet = orderID+orderValue
id=orderID
isAbstract = No
no parent
}
one sig orderID extends Integer{}
one sig orderValue extends Integer{}
one sig CustomerOrderAssociation extends Association{}{
src = Customer
dst = Order
src_multiplicity = ONE
dst_multiplicity = MANY
}
one sig ShippingCart extends Class{}{
attrSet = shippingCartID
id=shippingCartID
isAbstract = No
no parent
}
one sig shippingCartID extends Integer{}
one sig CustomerShippingCartAssociation extends Association{}{
src = Customer
dst = ShippingCart
src_multiplicity = ONE
dst_multiplicity = MANY
}
one sig Item extends Class{}{
attrSet = ItemID+quantity
id=ItemID
isAbstract = No
no parent
}
one sig ItemID extends Integer{}
one sig quantity extends Integer{}
one sig CartItem extends Class{}{
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
one sig OrderItem extends Class{}{
attrSet = orderItemID+status
id=orderItemID
isAbstract = No
parent in Item
}
one sig status extends Integer{}
one sig orderItemID extends Integer{}
some sig OrderItemAssociation extends Association{}{
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
one sig categoryName extends string{}
one sig ProductCategoryAssociation extends Association{}{
src = Product
dst = Category
src_multiplicity = MANY
dst_multiplicity = MANY
}
one sig Catalog extends Class{}{
attrSet = CatalogID
id=CatalogID
isAbstract = No
no parent
}
one sig CatalogID extends Integer{}
one sig ProductCatalogAssociation extends Association{}{
src = Product
dst = Catalog
src_multiplicity = ONE
dst_multiplicity = MANY
}
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
one sig productID extends Integer{}
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
one sig availability extends Bool{}
one sig ElectronicProduct extends Class{}{
attrSet = size
id=productID
isAbstract = No
parent in Product
}
one sig size extends string{}
one sig Service extends Class{}{
attrSet = schedule
id=productID
isAbstract = No
parent in Product
}
one sig schedule extends string{}
abstract one sig ProductAssetAssociation extends Association{}{
src = Product
dst = Asset
src_multiplicity = MANY
dst_multiplicity = MANY
}
one sig Asset extends Class{}{
attrSet = assetID+assetName+fileURI
id = assetID
isAbstract = No
no parent
}
lone sig assetID extends Integer{}
one sig assetName extends string{}
one sig fileURI extends string{}
one sig Media extends Class{}{
attrSet = mediaType
id = assetID
isAbstract = No
parent in Asset
}
one sig mediaType extends Integer{}
one sig Documents extends Class{}{
attrSet = excerpt
id = assetID
isAbstract = No
parent in Asset
}
one sig excerpt extends string{}
pred show{}
run show for 50
