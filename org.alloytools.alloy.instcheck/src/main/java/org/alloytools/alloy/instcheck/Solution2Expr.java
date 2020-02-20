package org.alloytools.alloy.instcheck;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import edu.mit.csail.sdg.ast.Attr;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.ast.Sig.PrimSig;
import edu.mit.csail.sdg.ast.Sig.SubsetSig;
import edu.mit.csail.sdg.translator.A4Solution;

public class Solution2Expr {

	private Map<String, Sig> atomSigs;
	private Map<Field, List<String>> tuples;

	public Expr getExpr(Module m, A4Solution sol) {
		if (!sol.satisfiable()) {
			return ExprConstant.FALSE;
		}

		Expr e = ExprConstant.TRUE;

		atomSigs = new HashMap<>();

		for (ExprVar ev : sol.getAllAtoms()) {
			String sigName = ev.type().toString().replace("{", "").replace("}", "");
			Sig s = getSig(m, sigName);

			if (s == null) {
				throw new RuntimeException("Signature for atom type " + sigName + " not found.");
			}

			if (s instanceof PrimSig) {
				String name = atom2SigName(ev.label);
				PrimSig newSig = new PrimSig(name, (PrimSig) s, Attr.ONE);
				atomSigs.put(ev.label, newSig);
			} else {
				throw new RuntimeException("Signature for atom type " + sigName + " not is not PrimSig (TODO).");
			}
		}
		e = e.and(union(m.getAllReachableUserDefinedSigs()).equal(union(atomSigs.values())));

		setUpTupleLists(m);

		findTuplesFromInst(sol);

		e = e.and(tupleRestrictions());

		return e;
	}

	private void findTuplesFromInst(A4Solution sol) {
		for (String line : sol.toString().split("\n")) {
			if (line.contains("<:")) {
				String tmp = line.split("<:")[1];
				String rel = tmp.split("=")[0];
				for (String tuple : tmp.split("=")[1].replace("{", "").replace("}", "").replace(" ", "").split(",")) {
					if (tuple.isEmpty()) {
						break;
					}
					Sig sig = atomSigs.get(tuple.split("->")[0]);
					Field f = findField(sig, rel);
					if (f == null) {
						throw new RuntimeException("Field " + rel + " does not exist in module.");
					}
					tuples.get(f).add(tuple);
				}
			}
		}
	}

	/**
	 * finds a field for the given relation or returns null if field is not found
	 * 
	 * @param sig
	 * @param rel
	 * @return
	 */
	private Field findField(Sig sig, String rel) {
		if (sig == null || sig.equals(Sig.UNIV)) {
			return null;
		}
		for (Field f : sig.getFields()) {
			if (f.label.equals(rel)) {
				return f;
			}
		}
		if (sig instanceof SubsetSig) {
			for (Sig p : ((SubsetSig) sig).parents) {
				Field f = findField(p, rel);
				if (f != null) {
					return f;
				}
			}
		} else if (sig instanceof PrimSig) {
			return findField(((PrimSig) sig).parent, rel);
		}
		return null;
	}

	/**
	 * restricts all fields to empty or to the set of tuples we found for them
	 * 
	 * @return
	 */
	private Expr tupleRestrictions() {
		Expr tr = ExprConstant.TRUE;
		for (Field f : tuples.keySet()) {
			Expr unionTs = null;
			for (String t : tuples.get(f)) {
				Expr tuple = null;
				for (String atom : t.split("->")) {
					if (tuple == null) {
						tuple = atomSigs.get(atom);
					} else {
						tuple = tuple.product(atomSigs.get(atom));
					}
				}

				if (unionTs == null) {
					unionTs = tuple;
				} else {
					unionTs = unionTs.plus(tuple);
				}
			}
			if (unionTs == null) {
				tr = tr.and(f.no());
			} else {
				tr = tr.and(f.equal(unionTs));
			}
		}
		return tr;
	}

	private void setUpTupleLists(Module m) {
		tuples = new LinkedHashMap<>();
		for (Sig s : m.getAllReachableSigs()) {
			for (Field f : s.getFields()) {
				tuples.put(f, new ArrayList<>());
			}
		}
	}

	/**
	 * FIXME potential naming clash if people use that in their signature names;
	 * 
	 * @param label
	 * @return
	 */
	private String atom2SigName(String label) {
		return label.replace("$", "_instance_");
	}

	private static Sig getSig(Module m, String name) {
		for (Sig s : m.getAllReachableUserDefinedSigs()) {
			if (s.label.equals(name)) {
				return s;
			}
		}
		return null;
	}

	/**
	 * union of the signatures in the list
	 * 
	 * @param sigs
	 * @return
	 */
	public Expr union(Collection<Sig> sigs) {
		Expr allAtoms = null;
		for (Sig s : sigs) {
			if (allAtoms == null) {
				allAtoms = s;
			} else {
				allAtoms = allAtoms.plus(s);
			}
		}
		if (allAtoms == null) {
			allAtoms = ExprConstant.EMPTYNESS;
		}
		return allAtoms;
	}

	public Collection<Sig> getAtomSigs() {
		return atomSigs.values();
	}

}
