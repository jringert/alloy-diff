# Differencing methodology algorithm
### 1.  Read both the versions into `Module` objects
### 2. Merge the Signatures
- From both the `Module` objects, create a key value pair (kvp) <signature name, signature object> for all the signatures in both versions into separate lists
- Read from the above kvps and create a list of merged signatures by adding all the signatures which have unique names in either kvp 

	##### ii. Create constraints from Signature attributes
	- strip attributes from the signature declaration and add them without any attributes
	- For other (changed) signatures, convert these signatures into constraints, so that instead of running them as signatures, we can combine them and run them as constraints on the model 
	- The type of attribute of the signature is checked and if the same is available in the attributes of the second signature, it is directly added
	- If the attributes are not same, we need to manually check and compare the types of attributes and create constraints based on the type of the attribute
	- For example, for an abstract signature, we create a constraint such that no instances of this signature are created in the instances of the merged model. The same is implied for other signature types.
	##### ii. Merge the fields under a signature
	-	__*To Do*__ 

### 3. Run the generated command with the generated merged signatures and their constraints to check if both the modules are consistent. 
---

## TO DO
##### Generation for: 
 - additional attributes
 - fields
 - assertions
 - facts
 - predicates
 - scopes and multiplicities
 
### Notes / Assumptions
- we assume that signatures with different names are different interms of semantics (this ignores renaming)


## Questions
- when checking for the operators of fields, as the operator fields are final, they are not updatable. so I have changed them to remove the final modifier on the Field object
- had to change constructor of Field from private to public