package org.alloytools.alloy.diff;

import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.ast.Sig.PrimSig;
import edu.mit.csail.sdg.ast.Sig.SubsetSig;

public class InheritanceUtil {
	/**
	 * map from original signatures to fields
	 */
	private Map<Sig, Set<Field>> allFields = new LinkedHashMap<Sig, Set<Field>>();

	/**
	 * all primitive signatures inheriting from the parent
	 */
	private Map<Sig, Set<Sig>> subSigs = new LinkedHashMap<Sig, Set<Sig>>();

	/**
	 * Fields that are contributed by subsetsignatures (stores most specific origin
	 * signature)
	 */
	private Set<Field> fieldsFromSubsetSig = new LinkedHashSet<>();

	public InheritanceUtil(Module m) {
		for (Sig s : m.getAllReachableSigs()) {
			if (s instanceof PrimSig && !s.builtin) {
				// add fields
				allFields.put(s, computeTransitiveExtendsFields(s));

				// add direct parents
				Sig parent = ((PrimSig) s).parent;
				if (parent != null && !parent.builtin) {
					Set<Sig> subs = subSigs.get(parent);
					if (subs == null) {
						subs = new LinkedHashSet<>();
						subSigs.put(parent, subs);
					}
					subs.add(s);
				}
			}
		}

		// compute transitive closure of children
		boolean changed = true;
		while (changed) {
			changed = false;
			for (Set<Sig> children : subSigs.values()) {
				Set<Sig> newSigs = new LinkedHashSet<>();
				for (Sig c : children) {
					if (subSigs.containsKey(c)) {
						newSigs.addAll(subSigs.get(c));
					}
				}
				if (!children.containsAll(newSigs)) {
					changed = true;
					children.addAll(newSigs);
				}

			}
		}

		// add fields contributed by SubsetSigs (to PrimSig parents and all their
		// children)
		for (Sig s : m.getAllReachableSigs()) {
			if (s instanceof SubsetSig && !s.builtin) {
				Set<Sig> flatParents = getFlattenedParents((SubsetSig) s);
				for (Field f : s.getFields()) {
					fieldsFromSubsetSig.add(f);
					for (Sig c : flatParents) {
						allFields.get(c).add(f);
					}
				}
			}
		}

	}

	/**
	 * computes all signatures that are parents of the subset signature s (includes
	 * inherited parents, e.g., SubSig-children of parents)
	 * 
	 * @param s
	 * @return
	 */
	public Set<Sig> getFlattenedParents(SubsetSig s) {
		Set<Sig> flatParents = new LinkedHashSet<>();
		if (!s.builtin) {
			Stack<Sig> pStack = new Stack<>();
			pStack.addAll(s.parents);
			while (!pStack.isEmpty()) {
				Sig p = pStack.pop();
				if (p instanceof SubsetSig) {
					pStack.addAll(((SubsetSig) p).parents);
				} else {
					flatParents.add(p);
					if (subSigs.get(p) != null) {
						flatParents.addAll(subSigs.get(p));
					}
				}
			}
		}
		return flatParents;
	}

	/**
	 * extends flattens from all transitive parent classes
	 * 
	 * @param s
	 * @return
	 */
	private Set<Field> computeTransitiveExtendsFields(Sig s) {
		Set<Field> fields = new LinkedHashSet<>();
		for (Field f : s.getFields()) {
			fields.add(f);
		}
		if (s instanceof PrimSig) {
			Sig parent = ((PrimSig) s).parent;
			if (parent != null) {
				fields.addAll(computeTransitiveExtendsFields(parent));
			}
		}
		return fields;
	}

	/**
	 * lookup field for a given signature by its name
	 * 
	 * @param s
	 * @param fName
	 * @return
	 */
	public Field getField(Sig s, String fName) {
		if (allFields.get(s) != null) {
			for (Field f : allFields.get(s)) {
				if (fName.equals(f.label)) {
					return f;
				}
			}
		}

		return null;
	}

	/**
	 * returns all fields (defined and inherited vis "extends") of this signature
	 * (PrimSig)
	 * 
	 * @param sig
	 * @return
	 */
	public Set<Field> getAllFields(Sig sig) {
		return allFields.get(sig);
	}

	/**
	 * returns all signatures (PrimSig) extending the parent signature.
	 * 
	 * @param parent
	 * @return null if no extending signatures exist
	 */
	public Set<Sig> getSubSigs(Sig parent) {
		return subSigs.get(parent);
	}
	
	/**
	 * get all top level signatures that have at least one child
	 * 
	 * @return
	 */
	public Set<Sig> getTopLvlSigsWithChildren() {
		Set<Sig> ts = new HashSet<>();
		ts.addAll(subSigs.keySet());
		for (Set<Sig> children : subSigs.values()) {
			ts.removeAll(children);
		}

		return ts;
	}

	/**
	 * get all signatures that have at least one child
	 * 
	 * @return
	 */
	public Set<Sig> getParentSigs() {
		Set<Sig> ps = new HashSet<>();
		ps.addAll(subSigs.keySet());
		return ps;
	}

	/**
	 * get parent signature
	 * 
	 * @return null if signature is its own parent
	 */
	public Sig getParentSig(Sig child) {
		Set<Sig> top = getTopLvlSigsWithChildren();
		if (top.contains(child)) {
			return null;
		}
		for (Sig parent : top) {
			if (subSigs.get(parent).contains(child)) {
				return parent;
			}
		}
		return null;
	}
	
	/**
	 * get all fields that are defined in SubsetSigs 
	 * @return
	 */
	public Set<Field> getFieldsFromSubsetSig() {
		return fieldsFromSubsetSig;
	}
}
