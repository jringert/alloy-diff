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
	-	done

### 3. Run the generated command with the generated merged signatures and their constraints to check if both the modules are consistent. 
---

## TO DO Implementation
 - improve GUI to understand what we actually solve "Find instance of ... that are not instances of ..." (Syed)
 - imports (Syed)
 - support inheritance
   - extends (Jan)
   - in
   - abstract signatures
 - inline facts of signatures with "implicit this"
 - assertions
 - run commands
 - scopes and typescopes
 - figure out the issue of ProductTypes and the case where arity > 1
 - fields of different arity
 
## TO DO Evaluation
 - get large numbers of Alloy specs with versions
 - set up more meaningfult test cases for correctness, e.g.,
   - every diff witness is an instance of module 2 

### Notes / Assumptions
- we assume that signatures with different names are different interms of semantics (this ignores renaming)

Take modules with extends

    sig AddressBook {
      entry : set Person
    } 

    sig Person {
      name : set Name
    }

    fact {
      all p : Person | #(p.name) = 2
    }

    sig Name {}

    sig Employee extends Person {}

    run {some b : Employee | b in AddressBook.entry}
    
Flattened to:
    
    sig AddressBook {
      entry : set Person + Employee
    } 

    sig Person {
      name : set Name
    }

    fact {
      all p : Person+Employee | #(p.(Person <: name + Employee <: name)) = 2
    }

    sig Name {}

    sig Employee {
      name : set Name
    }

    fact {
     # (Person + Employee) <= 3
    }

    run {some b : Employee | b in AddressBook.entry}