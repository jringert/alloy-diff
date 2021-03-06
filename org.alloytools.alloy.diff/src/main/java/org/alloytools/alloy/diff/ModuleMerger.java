package org.alloytools.alloy.diff;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.ast.Attr;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprCall;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.ExprITE;
import edu.mit.csail.sdg.ast.ExprLet;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprUnary.Op;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.ast.Sig.PrimSig;
import edu.mit.csail.sdg.ast.Sig.SubsetSig;
import edu.mit.csail.sdg.ast.Type;
import edu.mit.csail.sdg.ast.Type.ProductType;

public class ModuleMerger {

	/**
	 * merged signatures
	 */
	protected Map<String, Sig> sigs;
	/**
	 * optional, merged signature expressions for signatures from v1 (to simulate
	 * inheritance)
	 */
	protected Map<String, Expr> v1SigExpr;
	/**
	 * optional, merged field expressions for signatures from v1 (to simulate
	 * inheritance)
	 */
	protected Map<String, Expr> v1FieldExpr;
	/**
	 * inheritance information of v1 (not merged; on original signatures)
	 */
	protected InheritanceUtil v1iu;
	/**
	 * optional, merged signature expressions for signatures from v2 (to simulate
	 * inheritance)
	 */
	protected Map<String, Expr> v2SigExpr;
	/**
	 * optional, merged field expressions for signatures from v2 (to simulate
	 * inheritance)
	 */
	protected Map<String, Expr> v2FieldExpr;
	/**
	 * inheritance information of v2 (not merged; on original signatures)
	 */
	protected InheritanceUtil v2iu;
	/**
	 * constraints to ensure instances of v1 on merged signatures
	 */
	protected Expr c1;
	/**
	 * constraints to ensure instances of v2 on merged signatures
	 */
	protected Expr c2;

	protected Map<String, Sig> v1Sigs;
	protected Map<String, Sig> v2Sigs;

	/**
	 * workaround for Alloy bug on parsing and predicate pred/totalOrder
	 */
	private boolean inSigFactOfOrd = false;

	/**
	 * special flag for overriding signature references in fields when adding them
	 * to subsignatures
	 */
	private String sigOverrideForField;

	protected int maxInt;

	/**
	 * Merges signatures from v1 and v2 by creating combined Sigs for common
	 * signatures and copying unique signatures
	 *
	 * @param v1
	 * @param v2
	 * @return
	 */
	public Collection<Sig> mergeSigs(Module v1, Module v2) {
		/**
		 * merged signatures
		 */
		sigs = new LinkedHashMap<>();
		v1SigExpr = new LinkedHashMap<>();
		v1FieldExpr = new LinkedHashMap<>();
		v1iu = new InheritanceUtil(v1);
		v2SigExpr = new LinkedHashMap<>();
		v2FieldExpr = new LinkedHashMap<>();
		v2iu = new InheritanceUtil(v2);
		v1Sigs = new LinkedHashMap<>();
		v2Sigs = new LinkedHashMap<>();
		c1 = ExprConstant.TRUE;
		c2 = ExprConstant.TRUE;
		maxInt = 0;

		// fill look-up tables
		for (Sig s : v1.getAllReachableUserDefinedSigs()) {
			v1Sigs.put(s.toString(), s);
			if (s.label.endsWith("/Ord")) {
				throw new RuntimeException("Ordering not supported.");
			}
		}
		for (Sig s : v2.getAllReachableUserDefinedSigs()) {
			v2Sigs.put(s.toString(), s);
			if (s.label.endsWith("/Ord")) {
				throw new RuntimeException("Ordering not supported.");
			}
		}

		// do merge of signatures
		for (String sName : v1Sigs.keySet()) {
			if (v2Sigs.containsKey(sName) && !(v2Sigs.get(sName) instanceof SubsetSig)) {
				// create a merged signature
				Sig s1 = v1Sigs.get(sName);
				Sig s2 = v2Sigs.get(sName);
				if (s1 instanceof PrimSig && s2 instanceof PrimSig) {
					// ignore if both sigs are abstract and have subsigs
					if (!(s1.isAbstract != null && v1iu.getSubSigs(s1) != null && s2.isAbstract != null
							&& v2iu.getSubSigs(s2) != null)) {
						sigs.put(sName, mergeSig(s1, s2));
					}
				}
			} else {
				Sig old = v1Sigs.get(sName);
				// adding signatures that are unique in v1
				if (old instanceof PrimSig) {
					// check if needed: abstract sigs with children are not needed
					if (old.isAbstract == null || v1iu.getSubSigs(old) == null) {
						Sig s = null;
						if (old.isLone != null || old.isOne != null) {
							s = new PrimSig(sName, Attr.LONE);
						} else {
							s = new PrimSig(sName);
						}
						sigs.put(sName, s);
						c1 = generateSigAttributeConstraints(s, old, v1iu, c1);
						// closed world
						c2 = c2.and(s.no());
					}
				}
			}
		}
		for (String sName : v2Sigs.keySet()) {
			if (!v1Sigs.containsKey(sName) || v1Sigs.get(sName) instanceof SubsetSig) {
				Sig old = v2Sigs.get(sName);
				// adding signatures that are unique in v2
				if (old instanceof PrimSig) {
					if (old.isAbstract == null || v2iu.getSubSigs(old) == null) {
						Sig s = null;
						if (old.isLone != null || old.isOne != null) {
							s = new PrimSig(sName, Attr.LONE);
						} else {
							s = new PrimSig(sName);
						}
						sigs.put(sName, s);
						c2 = generateSigAttributeConstraints(s, old, v2iu, c2);
						// closed world
						c1 = c1.and(s.no());
					}
				}
			}
		}

		// calculate signature expressions by union of self and subclasses
		buildInheritanceSigExpr(v1, v1iu, v1SigExpr);
		buildInheritanceSigExpr(v2, v2iu, v2SigExpr);

		// INFO we don't support merging SubsetSig and PrimSig

		// create SubsetSig as union from both modules
		for (Sig s1 : v1Sigs.values()) {
			if (s1 instanceof SubsetSig) {
				Set<Sig> ps1 = parents((SubsetSig) s1);
				Sig s2 = v2Sigs.get(s1.label);
				if (s2 != null) {
					if (s2 instanceof SubsetSig) {
						Set<Sig> ps2 = parents((SubsetSig)s2);
						Set<Sig> union = new LinkedHashSet<>();
						union.addAll(ps1);
						union.addAll(ps2);

						SubsetSig sub = new SubsetSig(s1.label, union);
						sigs.put(s1.label, sub);
						
						// suppress additional sigs in each c1/c2
						Set<Sig> notInV1 = new LinkedHashSet<>();
						Set<Sig> notInV2 = new LinkedHashSet<>();
						notInV1.addAll(ps2);
						notInV1.removeAll(ps1);
						notInV2.addAll(ps1);
						notInV2.removeAll(ps2);
						for (Sig s : notInV1) {
							c1 = c1.and(s.in(sub).not());
						}
						for (Sig s : notInV2) {
							c2 = c2.and(s.in(sub).not());
						}
					} else {
						throw new RuntimeException("Cannot merge PrimSig and SubsetSig with same name: " + s1.label);
					}
				} else {
					// add v1 unique SubsetSig and suppress in v2 
					SubsetSig subV1 = new SubsetSig(s1.label, ps1);
					sigs.put(s1.label, subV1);
					c2 = c2.and(subV1.no());
				}
			}
		}
		// add v2 unique SubsetSig and suppress in v1 
		for (Sig s2 : v2Sigs.values()) {			
			if (s2 instanceof SubsetSig) {
				if (sigs.get(s2.label) == null) {
					Set<Sig> ps2 = parents((SubsetSig) s2);
					SubsetSig subV2 = new SubsetSig(s2.label, ps2);
					sigs.put(s2.label, subV2);
					c1 = c1.and(subV2.no());				
				} else if (sigs.get(s2.label) instanceof PrimSig) {
					throw new RuntimeException("Cannot merge PrimSig and SubsetSig with same name: " + s2.label);
				}
			}
		}

		// add containment of SubsetSigs in hierarchy:
		// for sig A in B ... {} add c1/c2 A in B
		// FIXME this must be that the child in the union of all its parents
		for (Sig s : v1Sigs.values()) {
			if (s instanceof SubsetSig) {
				SubsetSig sub = (SubsetSig) s;
				for (int i = 0; i < sub.parents.size(); i++) {
					Sig parent = sub.parents.get(i);
					if (parent instanceof SubsetSig) {
						Sig p = sigs.get(parent.label);
						Sig c = sigs.get(sub.label);
						c1 = c1.and(c.in(p));
					}
				}
			}
		}
		for (Sig s : v2Sigs.values()) {
			if (s instanceof SubsetSig) {
				SubsetSig sub = (SubsetSig) s;
				for (int i = 0; i < sub.parents.size(); i++) {
					Sig parent = sub.parents.get(i);
					if (parent instanceof SubsetSig) {
						Sig p = sigs.get(parent.label);
						Sig c = sigs.get(sub.label);
						c2 = c2.and(c.in(p));
					}
				}
			}
		}

		// add fields to merged signatures
		for (String sName : sigs.keySet()) {
			Sig s = sigs.get(sName);
			if (s instanceof PrimSig) {
				Sig s1 = v1Sigs.get(sName);
				Sig s2 = v2Sigs.get(sName);
				if (s1 != null && s2 != null) {
					mergeFields(s, mapOf(v1iu.getAllFields(s1)), mapOf(v2iu.getAllFields(s2)));
				} else if (s1 != null) {
					addFieldsOfUniqueSig(s, mapOf(v1iu.getAllFields(s1)), true);
				} else {
					addFieldsOfUniqueSig(s, mapOf(v2iu.getAllFields(s2)), false);
				}
			}
		}

		// calculate field expressions by union of fields with the same name of sub
		// signatures
		buildInheritanceFieldExpr(v1, v1iu, v1FieldExpr);
		buildInheritanceFieldExpr(v2, v2iu, v2FieldExpr);

		addSignatureFacts(v1, true);
		addSignatureFacts(v2, false);

		return sigs.values();
	}

	/**
	 * compute a set of transitive parent PrimSigs (merged sigs in new module)
	 * 
	 * @param sub1
	 * @return
	 */
	private Set<Sig> parents(SubsetSig sub1) {
		Set<Sig> parents = new LinkedHashSet<>();
		for (Sig p : v1iu.getFlattenedParents(sub1)) {
			Sig c = sigs.get(p.label);
			if (c != null) { // could be the case for abstract signatures
				parents.add(c);
			}
		}

		return parents;
	}

	private Map<String, Field> mapOf(Set<Field> allFields) {
		Map<String, Field> m = new LinkedHashMap<>();
		if (allFields != null) {
			for (Field f : allFields) {
				m.put(f.label, f);
			}
		}
		return m;
	}

	private void addSignatureFacts(Module orig, boolean inV1) {
		for (Sig os : orig.getAllReachableUserDefinedSigs()) {
			for (Expr of : os.getFacts()) {
				Expr mergedSig = replaceSigRefs(os, inV1);
				Decl thisDecl = mergedSig.oneOf("this");
				List<Decl> decls = new ArrayList<>();
				decls.add(thisDecl);
				if (os.label.endsWith("/Ord")) {
					inSigFactOfOrd = true;
				}
				Expr body = replaceSigRefs(of, decls, inV1);
				if (os.label.endsWith("/Ord")) {
					inSigFactOfOrd = false;
				}
				Expr sigFact = ExprQt.Op.ALL.make(of.pos, of.closingBracket, decls, body);
				if (inV1) {
					c1 = c1.and(sigFact);
				} else {
					c2 = c2.and(sigFact);
				}
			}
		}

	}

	/**
	 * calculate field expressions by union of fields with the same name of sub
	 * signatures and fieldexpressions for SubsetSigs 
	 * 
	 * @param m
	 * @param fieldExpr
	 */
	private void buildInheritanceFieldExpr(Module m, InheritanceUtil iu, Map<String, Expr> fieldExpr) {
		for (Sig owner : iu.getParentSigs()) {
			for (Field f : owner.getFields()) {
				String id = owner.label + "." + f.label;
				// field of new signature
				Expr fu = getField(sigs.get(owner.label), f.label);
				// all fields of children signatures
				for (Sig s : iu.getSubSigs(owner)) {
					if (fu == null) {
						fu = getField(sigs.get(s.label), f.label);
					} else {
						fu = fu.plus(getField(sigs.get(s.label), f.label));
					}
				}
				fieldExpr.put(id, fu);
			}
		}
		for (Field f : iu.getFieldsFromSubsetSig()) {
			Sig owner = f.sig;
			String id = owner.label + "." + f.label;
			Expr fu = null;
			for (Sig s : iu.getFlattenedParents((SubsetSig) owner)) {
				if (fu == null) {
					fu = getField(sigs.get(s.label), f.label);
				} else {
					fu = fu.plus(getField(sigs.get(s.label), f.label));
				}
			}
			fieldExpr.put(id, fu);
		}
	}

	private void buildInheritanceSigExpr(Module m, InheritanceUtil iu, Map<String, Expr> sigExpr) {
		for (Sig parent : m.getAllReachableUserDefinedSigs()) {
			if (parent instanceof SubsetSig) {
				Expr union = null;
				for (Sig s : iu.getFlattenedParents((SubsetSig) parent)) {
					// take care of null sigs that were not added
					if (sigs.get(s.label) != null) {
						if (union == null) {
							union = sigs.get(s.label);
						} else {
							union = union.plus(sigs.get(s.label));
						}
					}
				}
				sigExpr.put(parent.label, union);
			} else {
				Set<Sig> mSubSigs = iu.getSubSigs(parent);
				if (mSubSigs != null) {
					Expr union = sigs.get(parent.label);
					for (Sig s : mSubSigs) {
						// take care of null sigs that were not added
						if (sigs.get(s.label) != null) {
							if (union == null) {
								union = sigs.get(s.label);
							} else {
								union = union.plus(sigs.get(s.label));
							}
						}
					}
					sigExpr.put(parent.label, union);
				}
			}
		}
	}

	/**
	 * Creates a merged signature and adds constraints c1 c2 for individual sigs
	 *
	 * @param s1
	 * @param s2
	 * @return
	 */
	private Sig mergeSig(Sig s1, Sig s2) {
		Sig s = new PrimSig(s1.label, getCommonSigAttributes(s1, s2));
		c1 = generateSigAttributeConstraints(s, s1, v1iu, c1);
		c2 = generateSigAttributeConstraints(s, s2, v2iu, c2);

		return s;
	}

	/**
	 *
	 * TODO: only works for fields of the same arity as a workaround fields with
	 * lower arity could be padded with a singleton signature. However, this would
	 * require changing all expressions on fields.
	 * 
	 * FIXME the stack could run into a cycle: break the cycle by adding a field
	 * with its type (i.e., no syntactical restriction)
	 *
	 * @param mergedSig
	 * @param fields1
	 * @param fields2
	 */
	private void mergeFields(Sig mergedSig, Map<String, Field> fields1, Map<String, Field> fields2) {
		Set<String> fNames = new LinkedHashSet<String>();

		fNames.addAll(fields1.keySet());
		fNames.addAll(fields2.keySet());

		for (String fName : fNames) {
			Stack<String> fieldsToAdd = new Stack<>();
			if (getField(mergedSig, fName) == null) {
				fieldsToAdd.push(fName);
			}
			while (!fieldsToAdd.empty()) {
				String nextField = fieldsToAdd.peek();
				if (getField(mergedSig, nextField) == null) {
					try {
						sigOverrideForField = mergedSig.label;
						mergeField(mergedSig, fields1.get(nextField), fields2.get(nextField));
						sigOverrideForField = null;
						fieldsToAdd.pop();
					} catch (RuntimeException e) {
						if (e.getMessage() != null && e.getMessage().contains("Could not find merged field ")) {
							String missingField = e.getMessage().replace("Could not find merged field ", "");
							fieldsToAdd.push(missingField);
						} else {
							throw e;
						}
					}
				} else {
					fieldsToAdd.pop();
				}
			}
		}

	}

	private void mergeField(Sig mergedSig, Field f1, Field f2) {
		List<Decl> names = new ArrayList<>();
		names.add(mergedSig.decl);

		if (f1 != null && f2 != null) { // field is in both versions
			if (f1.decl().expr instanceof ExprUnary && f2.decl().expr instanceof ExprUnary) { // unary fields
				ExprUnary e1 = (ExprUnary) replaceSigRefs(f1.decl().expr, names, true);
				ExprUnary e2 = (ExprUnary) replaceSigRefs(f2.decl().expr, names, false);
				Field f;

				Expr union = e1.sub.isSame(e2.sub) ? e1.sub : e1.sub.plus(e2.sub);
				ExprUnary.Op op = getMergeOp(e1.op, e2.op);
				if (v1iu.getFieldsFromSubsetSig().contains(f1) || v2iu.getFieldsFromSubsetSig().contains(f2)) {
					op = getMergeOp(op, ExprUnary.Op.NO);
				}
				f = mergedSig.addField(f1.label, op.make(f1.pos, union));

				Decl ths = mergedSig.decl;
				Expr quantBody1 = ths.get().join(f).in(e1);
				if (v1iu.getFieldsFromSubsetSig().contains(f1)) {
					quantBody1 = ExprITE.make(f1.pos, ths.get().in(sigs.get(f1.sig.label)), quantBody1,
							ths.get().join(f).no());
				}
				Expr quantBody2 = ths.get().join(f).in(e2);
				if (v2iu.getFieldsFromSubsetSig().contains(f2)) {
					quantBody2 = ExprITE.make(f2.pos, ths.get().in(sigs.get(f2.sig.label)), quantBody2,
							ths.get().join(f).no());
				}
				Expr e1mult = ExprQt.Op.ALL.make(f1.pos, f1.closingBracket, List.of(ths), quantBody1);
				Expr e2mult = ExprQt.Op.ALL.make(f2.pos, f2.closingBracket, List.of(ths), quantBody2);

				c1 = c1.and(e1mult);
				c2 = c2.and(e2mult);
			} else if (f1.decl().expr instanceof ExprBinary && f2.decl().expr instanceof ExprBinary) { // relational
																										// fields
				Expr e1 = replaceSigRefs(f1.decl().expr, names, true);
				Expr e2 = replaceSigRefs(f2.decl().expr, names, false);
				Field f;
				if (e1.isSame(e2)) {
					f = mergedSig.addField(f1.label, e1);
				} else {
					Expr union = replaceArrows(e1).plus(replaceArrows(e2));
					f = mergedSig.addField(f1.label, union);

					Decl ths = mergedSig.decl;
					Expr quantBody1 = ths.get().join(f).in(e1);
					if (v1iu.getFieldsFromSubsetSig().contains(f1)) {
						quantBody1 = ExprITE.make(f1.pos, ths.get().in(sigs.get(f1.sig.label)),
								ths.get().join(f).in(e1), ths.get().join(f).no());
					}
					Expr quantBody2 = ths.get().join(f).in(e2);
					if (v2iu.getFieldsFromSubsetSig().contains(f2)) {
						quantBody2 = ExprITE.make(f2.pos, ths.get().in(sigs.get(f2.sig.label)),
								ths.get().join(f).in(e2), ths.get().join(f).no());
					}
					Expr e1mult = ExprQt.Op.ALL.make(f1.pos, f1.closingBracket, List.of(ths), quantBody1);
					Expr e2mult = ExprQt.Op.ALL.make(f2.pos, f2.closingBracket, List.of(ths), quantBody2);

					c1 = c1.and(e1mult);
					c2 = c2.and(e2mult);
				}
			} else {
				throw new RuntimeException("Mix of field arities " + f1.pos);
			}
		} else if (f1 != null) {
			addUniqueField(mergedSig, f1, true);
		} else if (f2 != null) {
			addUniqueField(mergedSig, f2, false);
		}
	}

	/**
	 * adding fields of a unique signature of eihter one version. No need to
	 * restrict c1 and c2 as instnaces of the signature wouldn't exist in the other
	 * version
	 * 
	 * @param s
	 * @param fields
	 * @param inV1
	 */
	private void addFieldsOfUniqueSig(Sig s, Map<String, Field> fields, boolean inV1) {
		for (String fName : fields.keySet()) {
			Stack<String> fieldsToAdd = new Stack<>();
			if (getField(s, fName) == null) {
				fieldsToAdd.push(fName);
			}
			while (!fieldsToAdd.empty()) {
				String nextField = fieldsToAdd.peek();
				if (getField(s, nextField) == null) {
					Field f = fields.get(nextField);
					try {
						sigOverrideForField = s.label;
						Expr bound = replaceSigRefs(f.decl().expr, List.of(s.decl), inV1);
						
						if ((inV1 ? v1iu : v2iu).getFieldsFromSubsetSig().contains(f)) {
							// we have a field from a SubsetSig
							if (bound instanceof ExprUnary) {
								// operator needs to be adapted
								Expr origBound = bound;
								ExprUnary.Op op = getMergeOp(((ExprUnary) bound).op, Op.NO);
								bound = op.make(f.pos, ((ExprUnary) bound).sub);
								// case 1: add the now optional field 
								Field merged = s.addField(f.label, bound);		
								if (inV1) {
									Decl ths = s.decl;
									Expr quantBody1 = ths.get().join(merged).in(origBound);
									quantBody1 = ExprITE.make(f.pos, ths.get().in(sigs.get(f.sig.label)),
											quantBody1, ths.get().join(merged).no());
									Expr e1mult = ExprQt.Op.ALL.make(f.pos, f.closingBracket, List.of(ths), quantBody1);
									c1 = c1.and(e1mult);
								} else {
									Decl ths = s.decl;
									Expr quantBody2 = ths.get().join(merged).in(origBound);
									quantBody2 = ExprITE.make(f.pos, ths.get().in(sigs.get(f.sig.label)),
											quantBody2, ths.get().join(merged).no());
									Expr e2mult = ExprQt.Op.ALL.make(f.pos, f.closingBracket, List.of(ths), quantBody2);
									c2 = c2.and(e2mult);
								}
							} else {
								// case 2: add relational field as is (it cannot have a multiplicity) 
								Field merged = s.addField(f.label, bound);
								// field needs to be suppressed
								if (inV1) {
									Decl ths = s.decl;
									Expr quantBody1 = ths.get().in(sigs.get(f.sig.label))
											.or(ths.get().join(merged).no());
									Expr e1mult = ExprQt.Op.ALL.make(f.pos, f.closingBracket, List.of(ths), quantBody1);
									c1 = c1.and(e1mult);
								} else {
									Decl ths = s.decl;
									Expr quantBody2 = ths.get().in(sigs.get(f.sig.label))
											.or(ths.get().join(merged).no());
									Expr e2mult = ExprQt.Op.ALL.make(f.pos, f.closingBracket, List.of(ths), quantBody2);
									c2 = c2.and(e2mult);
								}
							}
						} else {
							// case 3: just add field as is
							s.addField(f.label, bound);
						}
						sigOverrideForField = null;
						fieldsToAdd.pop();

					} catch (RuntimeException e) {
						if (e.getMessage() != null && e.getMessage().contains("Could not find merged field ")) {
							String missingField = e.getMessage().replace("Could not find merged field ", "");
							fieldsToAdd.push(missingField);
						} else {
							throw e;
						}
					}
				} else {
					fieldsToAdd.pop();
				}
			}
		}
	}

	/**
	 * adds a field to a common signature that only exists in v1 or v2 but not in
	 * both
	 * 
	 * @param mergedSig
	 * @param field
	 * @param inC1
	 */
	private void addUniqueField(Sig mergedSig, Field field, boolean inC1) {
		List<Decl> names = new ArrayList<>();
		names.add(mergedSig.decl);

		Field f;
		Expr e = replaceSigRefs(field.decl().expr, names, inC1);
		if (e instanceof ExprUnary) {
			ExprUnary.Op op = getMergeOp(((ExprUnary) e).op, ExprUnary.Op.NO);
			f = mergedSig.addField(field.label, op.make(field.pos, ((ExprUnary) e).sub));
			Decl ths = mergedSig.decl;
			if (inC1) {
				Expr quantBody = ths.get().join(f).in(e);
				// restriction of fields from SubsetSigs
				if (v1iu.getFieldsFromSubsetSig().contains(field)) {
					quantBody = ExprITE.make(field.pos, ths.get().in(sigs.get(field.sig.label)), quantBody,
							ths.get().join(f).no());
				}
				Expr e1mult = ExprQt.Op.ALL.make(field.pos, field.closingBracket, List.of(ths), quantBody);
				c1 = c1.and(e1mult);

				c2 = c2.and(f.decl().get().no());
			} else {
				c1 = c1.and(f.decl().get().no());

				Expr quantBody = ths.get().join(f).in(e);
				// restriction of fields from SubsetSigs
				if (v2iu.getFieldsFromSubsetSig().contains(field)) {
					quantBody = ExprITE.make(field.pos, ths.get().in(sigs.get(field.sig.label)), quantBody,
							ths.get().join(f).no());
				}

				Expr e2mult = ExprQt.Op.ALL.make(field.pos, field.closingBracket, List.of(ths), quantBody);
				c2 = c2.and(e2mult);
			}
		} else if (e instanceof ExprBinary) {
			f = mergedSig.addField(field.label, e);
			if (inC1) {
				if (v1iu.getFieldsFromSubsetSig().contains(field)) {
					Decl ths = mergedSig.decl;
					// make empty if not in SubsetSig
					Expr quantBody = ths.get().in(sigs.get(field.sig.label)).or(ths.get().join(f).no());
					Expr e1mult = ExprQt.Op.ALL.make(field.pos, field.closingBracket, List.of(ths), quantBody);
					c1 = c1.and(e1mult);
				}
				c2 = c2.and(f.decl().get().no());
			} else {
				if (v2iu.getFieldsFromSubsetSig().contains(field)) {
					Decl ths = mergedSig.decl;
					// make empty if not in SubsetSig
					Expr quantBody = ths.get().in(sigs.get(field.sig.label)).or(ths.get().join(f).no());
					Expr e2mult = ExprQt.Op.ALL.make(field.pos, field.closingBracket, List.of(ths), quantBody);
					c2 = c2.and(e2mult);
				}

				c1 = c1.and(f.decl().get().no());
			}
		}
	}

	private List<ExprHasName> replaceSigRefs(ConstList<? extends ExprHasName> es, boolean inV1) {
		List<ExprHasName> l = new ArrayList<>();
		for (Expr e : es) {
			l.add((ExprHasName) replaceSigRefs(e, inV1));
		}
		return l;
	}

	/**
	 * Replaces occurrences of old signatures in the expression by the merged
	 * signatures
	 *
	 * @param expr
	 * @return
	 */
	protected Expr replaceSigRefs(Expr expr, boolean inV1) {
		return replaceSigRefs(expr, new ArrayList<>(), inV1);
	}

	/**
	 * Replaces occurrences of old signatures in the expression by the merged
	 * signatures
	 *
	 * @param expr
	 * @param names list of local names to use for ExprVar
	 * @return
	 */
	private Expr replaceSigRefs(Expr expr, List<Decl> names, boolean inV1) {
		switch (expr.getClass().getSimpleName()) {
		case "ExprUnary":
			ExprUnary ue = (ExprUnary) expr;
			return ue.op.make(ue.pos, replaceSigRefs(ue.sub, List.copyOf(names), inV1));
		case "ExprBinary":
			ExprBinary be = (ExprBinary) expr;
			return be.op.make(be.pos, be.closingBracket, replaceSigRefs(be.left, List.copyOf(names), inV1),
					replaceSigRefs(be.right, List.copyOf(names), inV1));
		case "PrimSig":
			PrimSig ps = (PrimSig) expr;
			// workaround for totalOrder bug
			if (inSigFactOfOrd && ps.label.endsWith("/Ord")) {
				for (Decl d : names) {
					for (ExprHasName n : d.names) {
						if (n.label.equals("this")) {
							return n;
						}
					}
				}
			}
			// expressions taking care of inheritance override normal signatures
			if (inV1 && v1SigExpr.get(ps.label) != null) {
				return v1SigExpr.get(ps.label);
			} else if (!inV1 && v2SigExpr.get(ps.label) != null) {
				return v2SigExpr.get(ps.label);
			}
			// return merged signature
			Sig s = sigs.get(ps.label);
			if (s == null) {
				s = getInternalSig(ps.label);
				if (s == null) {
					throw new RuntimeException("Could not find merged signarure " + ps.label);
				}
			}
			return s;
		case "SubsetSig":
			SubsetSig sub = (SubsetSig) expr;
			return sigs.get(sub.label);
		case "ExprList":
			ExprList el = (ExprList) expr;
			List<Expr> l = new ArrayList<Expr>();
			for (Expr e : el.args) {
				l.add(replaceSigRefs(e, List.copyOf(names), inV1));
			}
			return ExprList.make(el.pos, el.closingBracket, el.op, l);
		case "ExprQt":
			ExprQt eq = (ExprQt) expr;
			List<Decl> allDecls = new ArrayList<Decl>(names);
			List<Decl> qtDecls = new ArrayList<Decl>();
			for (Decl d : eq.decls) {
				Decl newD = new Decl(d.isPrivate, d.disjoint, d.disjoint2, replaceSigRefs(d.names, inV1),
						replaceSigRefs(d.expr, allDecls, inV1));
				qtDecls.add(newD);
				allDecls.add(newD);
			}
			return eq.op.make(eq.pos, eq.closingBracket, qtDecls, replaceSigRefs(eq.sub, allDecls, inV1));
		case "ExprVar":
			ExprVar ev = (ExprVar) expr;
			for (Decl d : names) {
				for (ExprHasName n : d.names) {
					if (n.label.equals(ev.label)) {
						return n;
					}
				}
			}
			Type t = ev.type();
			if (ev.label.equals("this")) {
				// TODO check whether this is always right
				return getExprVarToSig(ev);
			}
			ExprVar ret = ExprVar.make(ev.pos, ev.label, replaceSigRefs(t, inV1));
			return ret;
		case "Field":
			Field f = (Field) expr;
			String sigName = sigOverrideForField != null ? sigOverrideForField : f.sig.label;
			// check whether we have field expressions to take care of inheritance
			String key = sigName + "." + f.label;
			if (inV1 && v1FieldExpr.get(key) != null) {
				return v1FieldExpr.get(key);
			} else if (!inV1 && v2FieldExpr.get(key) != null) {
				return v2FieldExpr.get(key);
			}
			// return reference to merged field
			Expr res = getField(sigs.get(sigName), f.label);
			if (res == null) {
				throw new RuntimeException("Could not find merged field " + f.label);
			}
			return res;
		case "ExprConstant":
			maxInt = Math.max(maxInt, ((ExprConstant) expr).num());
			return expr;
		case "ExprCall":
			//
			ExprCall ec = (ExprCall) expr;
			List<Expr> args = new ArrayList<>();
			for (Expr c : ec.args) {
				args.add(replaceSigRefs(c, names, inV1));
			}
			// FIXME pass names as parameter?
			Expr nec = ExprCall.make(ec.pos, ec.closingBracket, replaceSigRefs(ec.fun, inV1), args, 0);
			return nec;
		case "ExprLet":
			ExprLet let = (ExprLet) expr;
			ExprVar evar = (ExprVar) replaceSigRefs(let.var, inV1);

			List<ExprHasName> letNames = new ArrayList<>();
			letNames.add(evar);
			Decl d = new Decl(null, null, null, letNames, evar);
			names = new ArrayList<>(names);
			names.add(d);
			return ExprLet.make(let.pos, evar, replaceSigRefs(let.expr, names, inV1),
					replaceSigRefs(let.sub, names, inV1));
		case "ExprITE":
			ExprITE ite = (ExprITE) expr;
			return ExprITE.make(ite.pos, replaceSigRefs(ite.cond, List.copyOf(names), inV1),
					replaceSigRefs(ite.left, List.copyOf(names), inV1),
					replaceSigRefs(ite.right, List.copyOf(names), inV1));
		default:
			System.out.println(expr.getClass().getSimpleName());
			throw new RuntimeException(
					"Error in replaceSigRefs for: " + expr.getClass().getSimpleName() + "\nat " + expr.pos);
		}
	}

	private Func replaceSigRefs(Func fun, boolean inV1) {
		List<Decl> decls = new ArrayList<Decl>();
		// FIXME some functions have a decl that refernces a signature as this
		// ..\models-master\ietf-rfcs\rfc7617-BasicAuth\basic-auth.als
		// fun Charset.binary[ s : String ] : Binary {this.maps[s]}
		for (Decl d : fun.decls) {
			decls.add(new Decl(d.isPrivate, d.disjoint, d.disjoint2, replaceSigRefs(d.names, inV1),
					replaceSigRefs(d.expr, inV1)));
		}
		Func fun2 = new Func(fun.pos, fun.label, decls, replaceSigRefs(fun.returnDecl, decls, inV1),
				replaceSigRefs(fun.getBody(), decls, inV1));
		return fun2;
	}

	private ExprVar getExprVarToSig(ExprVar ev) {
		ProductType pt = ev.type().iterator().next();
		if (pt.arity() > 1) {
			throw new RuntimeException("Arity > 1 when resolving a \"this\" expression");
		}
		// FIXME this might need to look up the signature expression instead
		Sig s = sigs.get(pt.get(0).label);
		if (s == null) {
			s = getInternalSig(pt.get(0).label);
			if (s == null) {
				throw new RuntimeException("Signature " + pt.get(0).label + " not found in merged signature map.");
			}
		}

		return (ExprVar) s.decl.get();
	}

	private Type replaceSigRefs(Type t, boolean inV1) {
		for (ProductType pt : t) {
			Type product = null;
			for (int i = 0; i < pt.arity(); i++) {
				Expr s = (inV1 ? v1SigExpr : v2SigExpr).get(pt.get(i).label);
				if (s == null) {
					s = sigs.get(pt.get(i).label);
				}
				if (s == null) {
					s = getInternalSig(pt.get(i).label);
					if (s == null) {
						throw new RuntimeException(
								"Signature " + pt.get(i).label + " not found in merged signature map.");
					}
				}
				if (product == null) {
					product = s.type();
				} else {
					product = product.product(s.type());
				}
			}
			return product;
		}
		if (t.is_bool) {
			return Type.FORMULA;
		}
		throw new RuntimeException("Unhandled case at end of replaceSigRefs(Type t)");
	}

	private Sig getInternalSig(String label) {
		switch (label) {
		case "univ":
			return Sig.UNIV;
		case "Int":
			return Sig.SIGINT;
		case "seq/Int":
			return Sig.SEQIDX;
		case "String":
			return Sig.STRING;
		case "none":
			return Sig.NONE;
		default:
			return null;
		}

	}

	private Expr getField(Sig sig, String label) {
		if (sig != null) {
			for (Field f : sig.getFields()) {
				if (f.label.equals(label)) {
					return f;
				}
			}
		}
		return null;
	}

	/**
	 * replaces any arrow inside binary expressions by the default arrow "->"
	 * 
	 * IMPORTANT this operates on already merged and replaced expressions
	 * 
	 * some expressions (that may not contain arrows are returned as is)
	 *
	 * @param expr
	 * @return
	 */
	private Expr replaceArrows(Expr expr) {
		switch (expr.getClass().getSimpleName()) {
		case "ExprUnary":
			ExprUnary ue = (ExprUnary) expr;
			return ue.op.make(ue.pos, replaceArrows(ue.sub));
		case "ExprBinary":
			ExprBinary be = (ExprBinary) expr;
			if (be.op.isArrow) {
				return ExprBinary.Op.ARROW.make(be.pos, be.closingBracket, replaceArrows(be.left),
						replaceArrows(be.right));
			} else {
				return be.op.make(be.pos, be.closingBracket, replaceArrows(be.left), replaceArrows(be.right));
			}
		case "ExprList":
			ExprList el = (ExprList) expr;
			List<Expr> l = new ArrayList<Expr>();
			for (Expr e : el.args) {
				l.add(replaceArrows(e));
			}
			return ExprList.make(el.pos, el.closingBracket, el.op, l);
		case "PrimSig":
			return expr;
		case "Field":
			return expr;
		case "ExprVar":
			return expr;
		case "ExprQt":
			return expr;
		case "ExprConstant":
			return expr;
		default:
			throw new RuntimeException(
					"replaceArrows(..) unhandled expr: " + expr.getClass().getSimpleName() + " in " + expr.pos);
		}
	}

	/**
	 * Computes least upper bound of two operators
	 *
	 * @param op
	 * @param op2
	 * @return
	 */
	private ExprUnary.Op getMergeOp(ExprUnary.Op op, ExprUnary.Op op2) {
		switch (op) {
		case SETOF:
			return ExprUnary.Op.SETOF;
		case SOMEOF:
			switch (op2) {
			case SETOF:
				return ExprUnary.Op.SETOF;
			case LONEOF:
				return ExprUnary.Op.SETOF;
			case NO:
				return ExprUnary.Op.SETOF;
			default:
				// this covers both the some and the one operator
				return ExprUnary.Op.SOMEOF;
			}
		case LONEOF:
			switch (op2) {
			case SETOF:
				return ExprUnary.Op.SETOF;
			case SOMEOF:
				return ExprUnary.Op.SETOF;
			default:
				// this covers both the lone and the one operator
				return ExprUnary.Op.LONEOF;
			}
		case ONEOF:
			switch (op2) {
			case SETOF:
				return ExprUnary.Op.SETOF;
			case SOMEOF:
				return ExprUnary.Op.SOMEOF;
			case LONEOF:
				return ExprUnary.Op.LONEOF;
			case NO:
				return ExprUnary.Op.LONEOF;
			default:
				// this covers the one operator
				return ExprUnary.Op.ONEOF;
			}
		case NO:
			switch (op2) {
			case SETOF:
				return ExprUnary.Op.SETOF;
			case SOMEOF:
				return ExprUnary.Op.SETOF;
			case LONEOF:
				return ExprUnary.Op.LONEOF;
			case NO:
				return ExprUnary.Op.NO;
			case ONEOF:
				return ExprUnary.Op.LONEOF;
			default:
				// this covers the one operator
				return ExprUnary.Op.NO;
			}
		default:
			return ExprUnary.Op.SETOF;
		}
	}

	/**
	 * create constraints for attributes
	 *
	 * @param s
	 * @param old
	 * @param c
	 * @return
	 */
	private Expr generateSigAttributeConstraints(Sig s, Sig old, InheritanceUtil iu, Expr c) {

		if (old.isAbstract != null && s.isAbstract == null) {
			// without inheritance, abstract has no impact
			if (iu.getSubSigs(old) != null) {
				c = c.and(s.no());
			}
		}

		if (old.isLone != null && s.isLone == null) {
			c = c.and(s.lone());
		}

		if (old.isOne != null && s.isOne == null) {
			c = c.and(s.one());
		}

		if (old.isSome != null && s.isSome == null) {
			c = c.and(s.some());
		}

		return c;
	}

	/**
	 * keep all common attributes FIXME for multiplicities is should be better to
	 * take the least upper bound
	 * 
	 * @param s1
	 * @param s2
	 * @return
	 */
	private Attr[] getCommonSigAttributes(Sig s1, Sig s2) {
		List<Attr> attrs = new ArrayList<>();
		for (Attr a1 : s1.attributes) {
			for (Attr a2 : s2.attributes) {
				if (a1 != null && a2 != null && a1.type.equals(a2.type)) {
					attrs.add(a1.type.make(a1.pos));
				}
			}
		}
		return attrs.toArray(new Attr[] {});
	}

}
