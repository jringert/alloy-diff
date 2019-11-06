# Differencing methodology algorithm
### 1.  Read both the versions into `Module` objects
### 2. Merge the Signatures
- From both the `Module` objects, create a key value pair (kvp) <signature name, signature object> for all the signatures in both versions into separate lists
- Read from the above kvps and create a list of merged signatures by adding all the signatures which are unique in either kvp

	##### ii. Create constraints from Signature attributes
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