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
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.ast.Sig.PrimSig;
import edu.mit.csail.sdg.translator.A4Solution;

public class Solution2Expr {

	private Map<String, Sig> atomSigs;
	private Map<Field, List<String>> tuples;

	private FieldUtil fieldUtil;

	public Expr getExpr(Collection<Sig> sigs, A4Solution sol) {
		if (!sol.satisfiable()) {
			return ExprConstant.FALSE;
		}
		
		Map<String, Sig> sigByName = new LinkedHashMap<>();
		for (Sig sig : sigs) {
			sigByName.put(sig.label, sig);
		}

		Expr e = ExprConstant.TRUE;

		fieldUtil = new FieldUtil(sigs);
		atomSigs = new HashMap<>();

		for (ExprVar ev : sol.getAllAtoms()) {
			Sig s = sigByName.get(ev.type().iterator().next().get(0).label);

			if (s instanceof PrimSig) {
				if (s.isEnum != null) {					
					atomSigs.put(ev.label, enumSig(sigs, ev.label));	
				} else {
					String name = atom2SigName(ev.label);
					PrimSig newSig = new PrimSig(name, (PrimSig) s, Attr.ONE);
					atomSigs.put(ev.label, newSig);
				}
			} else {
				throw new RuntimeException("Signature " + s + " for atom type is not PrimSig (TODO).");
			}
		}
		e = e.and(union(sigs).equal(union(atomSigs.values())));

		setUpTupleLists(sigs);

		findTuplesFromInst(sol);

		e = e.and(tupleRestrictions());

		return e;
	}

	private Sig enumSig(Collection<Sig> sigs, String label) {
		String eName = label.split("\\$")[0];
		if (!eName.contains("/")) {
			eName = "this/" + eName;
		}
		for (Sig e : sigs) {
			if (eName.equals(e.label)) {
				return e;
			}
		}
		return null;
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
	 * NOTE: This code sometimes needs to unpack the signature before using the FieldUtils
	 * class (the current signature is a child of a signature from the module).
	 * 
	 * @param sig
	 * @param rel
	 * @return
	 */
	private Field findField(Sig sig, String rel) {
		if (sig == null || sig.equals(Sig.UNIV)) {
			return null;
		}

		return fieldUtil.getField(((PrimSig) sig).parent, rel);
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
						if (atom.startsWith("\"")) {
							tuple = tuple.product(ExprConstant.Op.STRING.make(null, atom));
						} else if (isInteger(atom)){
							tuple = tuple.product(ExprConstant.Op.NUMBER.make(null, Integer.parseInt(atom)));
						} else {
							tuple = tuple.product(atomSigs.get(atom));
						}
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

	private boolean isInteger(String atom) {
		try {
			Integer.parseInt(atom);
		} catch (NumberFormatException e) {
			return false;
		}
		return true;
	}

	private void setUpTupleLists(Collection<Sig> sigs) {
		tuples = new LinkedHashMap<>();
		for (Sig s : sigs) {
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
