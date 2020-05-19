package org.alloytools.alloy.diff;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.ast.Attr;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.CommandScope;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprCall;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.ExprITE;
import edu.mit.csail.sdg.ast.ExprLet;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprList.Op;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.ast.Sig.PrimSig;
import edu.mit.csail.sdg.ast.Type;
import edu.mit.csail.sdg.ast.Type.ProductType;
import examples.alloy.Lists;

public class ModuleMerger {

	/**
	 * merged signatures
	 */
	protected static Map<String, Sig> sigs;
	/**
	 * optional, merged signature expressions for signatures from v1 (to simulate
	 * inheritance)
	 */
	protected static Map<String, Expr> v1SigExpr;
	/**
	 * optional, merged field expressions for signatures from v1 (to simulate
	 * inheritance)
	 */
	protected static Map<String, Expr> v1FieldExpr;
	/**
	 * inheritance information of v1 (not merged; on original signatures)
	 */
	protected static InheritanceUtil v1iu;
	/**
	 * optional, merged signature expressions for signatures from v2 (to simulate
	 * inheritance)
	 */
	protected static Map<String, Expr> v2SigExpr;
	/**
	 * optional, merged field expressions for signatures from v2 (to simulate
	 * inheritance)
	 */
	protected static Map<String, Expr> v2FieldExpr;
	/**
	 * inheritance information of v2 (not merged; on original signatures)
	 */
	protected static InheritanceUtil v2iu;
	/**
	 * constraints to ensure instances of v1 on merged signatures
	 */
	protected static Expr c1;
	/**
	 * constraints to ensure instances of v2 on merged signatures
	 */
	protected static Expr c2;

	protected static Map<String, Sig> v1Sigs;
	protected static Map<String, Sig> v2Sigs;
	
	/**
	 * Merges signatures from v1 and v2 by creating combined Sigs for common
	 * signatures and copying unique signatures
	 *
	 * @param v1
	 * @param v2
	 * @return
	 */
	public static Collection<Sig> mergeSigs(Module v1, Module v2) {
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

		// fill look-up tables
		for (Sig s : v1.getAllReachableUserDefinedSigs()) {
			v1Sigs.put(s.toString(), s);
		}
		for (Sig s : v2.getAllReachableUserDefinedSigs()) {
			v2Sigs.put(s.toString(), s);
		}

		// do merge
		for (String sName : v1Sigs.keySet()) {
			if (v2Sigs.containsKey(sName)) {
				// create a merged signature
				Sig s1 = v1Sigs.get(sName);
				Sig s2 = v2Sigs.get(sName);
				if (s1 instanceof PrimSig && s2 instanceof PrimSig) {
					// ignore if both sigs are abstract and have subsigs
					if (!(s1.isAbstract != null && v1iu.getSubSigs(s1) != null && s2.isAbstract != null
							&& v1iu.getSubSigs(s2) != null)) {
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
			if (!v1Sigs.containsKey(sName)) {
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

		for (String sName : sigs.keySet()) {
			Sig s = sigs.get(sName);
			// TODO check what happens to subsignatures
			Sig s1 = v1Sigs.get(sName);
			Sig s2 = v2Sigs.get(sName);
			if (s1 != null && s2 != null) {
				mergeFields(s, v1iu.getAllFields(s1), v2iu.getAllFields(s2));
			} else if (s1 != null) {
				addFields(s, v1iu.getAllFields(s1), true);
			} else {
				addFields(s, v2iu.getAllFields(s2), false);
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

	private static void addSignatureFacts(Module orig, boolean inV1) {
		for (Sig os : orig.getAllReachableUserDefinedSigs()) {
			for (Expr of : os.getFacts()) {
				Expr mergedSig = replaceSigRefs(os, inV1);
				Decl thisDecl = mergedSig.oneOf("this");
				List<Decl> decls = new ArrayList<>();
				decls.add(thisDecl);
				Expr body = replaceSigRefs(of, decls, inV1);
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
	 * signatures
	 * 
	 * @param m
	 * @param fieldExpr
	 */
	private static void buildInheritanceFieldExpr(Module m, InheritanceUtil iu, Map<String, Expr> fieldExpr) {
		for (Sig owner : iu.getParentSigs()) {
			for (Field f : owner.getFields()) {
				String id = owner.label + "." + f.label;
				// field of new signature
				Expr fu = getField(sigs.get(owner.label), f.label);
				// all fields of children signatures
				for (Sig s : iu.getSubSigs(owner)) {
					if (iu.getSubSigs(owner) != null) {
						if (fu == null) {
							fu = getField(sigs.get(s.label), f.label);
						} else {
							fu = fu.plus(getField(sigs.get(s.label), f.label));
						}
					}
				}
				fieldExpr.put(id, fu);
			}
		}
	}

	private static void buildInheritanceSigExpr(Module m, InheritanceUtil iu, Map<String, Expr> sigExpr) {
		for (Sig parent : m.getAllReachableUserDefinedSigs()) {
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

	/**
	 * Creates a merged signature and adds constraints c1 c2 for individual sigs
	 *
	 * @param s1
	 * @param s2
	 * @return
	 */
	private static Sig mergeSig(Sig s1, Sig s2) {
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
	 * TODO: messes up with field references inside field declarations; check this!
	 * -- probably fine due to order in which fields are declared and due to
	 * restrictions in c1 and c2
	 * 
	 * FIXME: restrictions for c1 and c2 dont work when they are referencing fields
	 * (syntactically) New idea: use types to create signature of fields -- looses
	 * LUP then construct constraints by quantification over instances -> body of
	 * quantification should follow from field expression
	 *
	 * @param mergedSig
	 * @param fields1
	 * @param fields2
	 */
	private static void mergeFields(Sig mergedSig, Set<Field> fields1, Set<Field> fields2) {
		Set<Field> unique1 = new LinkedHashSet<Sig.Field>();
		Set<Field> unique2 = new LinkedHashSet<Sig.Field>();

		for (Field f1 : fields1) {
			unique1.add(f1);
		}
		for (Field f2 : fields2) {
			unique2.add(f2);
		}

		List<Decl> names = new ArrayList<>();
		names.add(mergedSig.decl);

		for (Field f1 : fields1) {
			for (Field f2 : fields2) {
				if (f1.label.equals(f2.label)) {
					// FIXME the following check is likely too heuristic, there might be a unary
					// expression containing further arrows
					if (f1.decl().expr instanceof ExprUnary && f2.decl().expr instanceof ExprUnary) {
						ExprUnary e1 = (ExprUnary) replaceSigRefs(f1.decl().expr, names, true);
						ExprUnary e2 = (ExprUnary) replaceSigRefs(f2.decl().expr, names, false);
						Expr union = e1.sub.plus(e2.sub);
						ExprUnary.Op op = getMergeOp(e1.op, e2.op);
						Field f = mergedSig.addField(f1.label, op.make(f1.pos, union));

//						Expr e1mult = getArrowForOp(e1.op).make(f1.pos, f1.closingBracket, mergedSig, e1.sub);
//						Expr e2mult = getArrowForOp(e2.op).make(f2.pos, f2.closingBracket, mergedSig, e2.sub);
//						c1 = c1.and(f.decl().get().in(e1mult));
//						c2 = c2.and(f.decl().get().in(e2mult));

						unique1.remove(f1);
						unique2.remove(f2);
						break;
					} else if (f1.decl().expr instanceof ExprBinary && f2.decl().expr instanceof ExprBinary) {
						Expr e1 = replaceSigRefs(f1.decl().expr, names, true);
						Expr e2 = replaceSigRefs(f2.decl().expr, names, false);
						Expr union = replaceArrows(e1).plus(replaceArrows(e2));
						Field f = mergedSig.addField(f1.label, union);

//						Expr e1mult = ExprBinary.Op.ARROW.make(f1.pos, f1.closingBracket, mergedSig, e1);
//						Expr e2mult = ExprBinary.Op.ARROW.make(f2.pos, f2.closingBracket, mergedSig, e2);
//						c1 = c1.and(f.decl().get().in(e1mult));
//						c2 = c2.and(f.decl().get().in(e2mult));

						unique1.remove(f1);
						unique2.remove(f2);

					} else {
						throw new RuntimeException("Mix of field arities " + f1.pos);
					}
				}
			}
		}

		for (Field f : unique1) {
			addUniqueField(mergedSig, f, true);
		}
		for (Field f : unique2) {
			addUniqueField(mergedSig, f, false);
		}
	}

	private static void addFields(Sig s, Set<Field> fields, boolean inV1) {
		List<Decl> names = new ArrayList<>();
		names.add(s.decl);
		for (Field f : fields) {
			s.addField(f.label, replaceSigRefs(f.decl().expr, names, inV1));
		}
	}

	private static void addUniqueField(Sig mergedSig, Field field, boolean inC1) {
		List<Decl> names = new ArrayList<>();
		names.add(mergedSig.decl);

		Field f;
		Expr e = replaceSigRefs(field.decl().expr, names, inC1);
		if (e instanceof ExprUnary) {
			ExprUnary.Op op = getMergeOp(((ExprUnary) e).op, ExprUnary.Op.SETOF);
			f = mergedSig.addField(field.label, op.make(field.pos, ((ExprUnary) e).sub));
			if (inC1) {
				Expr e1mult = getArrowForOp(((ExprUnary) e).op).make(field.pos, field.closingBracket, mergedSig,
						((ExprUnary) e).sub);
				c1 = c1.and(f.decl().get().in(e1mult));
				c2 = c2.and(f.decl().get().no());
			} else {
				c1 = c1.and(f.decl().get().no());
				Expr e2mult = getArrowForOp(((ExprUnary) e).op).make(field.pos, field.closingBracket, mergedSig,
						((ExprUnary) e).sub);
				c2 = c2.and(f.decl().get().in(e2mult));
			}
		} else if (e instanceof ExprBinary) {
			f = mergedSig.addField(field.label, e);
			if (inC1) {
				Expr e1mult = ExprBinary.Op.ARROW.make(field.pos, field.closingBracket, mergedSig, e);
				c1 = c1.and(f.decl().get().in(e1mult));
				c2 = c2.and(f.decl().get().no());
			} else {
				c1 = c1.and(f.decl().get().no());
				Expr e2mult = ExprBinary.Op.ARROW.make(field.pos, field.closingBracket, mergedSig, e);
				c2 = c2.and(f.decl().get().in(e2mult));
			}
		}
	}

	private static List<ExprHasName> replaceSigRefs(ConstList<? extends ExprHasName> es, boolean inV1) {
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
	private static Expr replaceSigRefs(Expr expr, boolean inV1) {
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
	private static Expr replaceSigRefs(Expr expr, List<Decl> names, boolean inV1) {
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
			// FIXME figure out how to correctly use the this reference in signatures where
			// one field references the ohter
			if (ev.label.equals("this")) {
				System.err.println("FIXME");
				return getExprVarToSig(ev);
			}
			ExprVar ret = ExprVar.make(ev.pos, ev.label, replaceSigRefs(t, inV1));
			return ret;
		case "Field":
			Field f = (Field) expr;
			// check whether we have field expressions to take care of inheritance
			String key = f.sig.label + "." + f.label;
			if (inV1 && v1FieldExpr.get(key) != null) {
				return v1FieldExpr.get(key);
			} else if (!inV1 && v2FieldExpr.get(key) != null) {
				return v2FieldExpr.get(key);
			}
			// return reference to merged field
			Expr res = getField(sigs.get(f.sig.label), f.label);
			if (res == null) {
				throw new RuntimeException("Could not find merged field " + f.label);
			}
			return res;
		case "ExprConstant":
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
			return ExprLet.make(let.pos, evar, replaceSigRefs(let.expr, names, inV1), replaceSigRefs(let.sub, names, inV1));
		case "ExprITE":
			ExprITE ite = (ExprITE) expr;
			return ExprITE.make(ite.pos, replaceSigRefs(ite.cond, List.copyOf(names), inV1),
					replaceSigRefs(ite.left, List.copyOf(names), inV1), replaceSigRefs(ite.right, List.copyOf(names), inV1));
		default:
			System.out.println(expr.getClass().getSimpleName());
			throw new RuntimeException(
					"Error in replaceSigRefs for: " + expr.getClass().getSimpleName() + "\nat " + expr.pos);
		}
	}

	private static Func replaceSigRefs(Func fun, boolean inV1) {
		List<Decl> decls = new ArrayList<Decl>();
		// FIXME some functions have a decl that refernces a signature as this
		// ..\models-master\ietf-rfcs\rfc7617-BasicAuth\basic-auth.als
		// fun Charset.binary[ s : String ] : Binary {this.maps[s]}
		for (Decl d : fun.decls) {
			decls.add(
					new Decl(d.isPrivate, d.disjoint, d.disjoint2, replaceSigRefs(d.names, inV1), replaceSigRefs(d.expr, inV1)));
		}
		Func fun2 = new Func(fun.pos, fun.label, decls, replaceSigRefs(fun.returnDecl, decls, inV1),
				replaceSigRefs(fun.getBody(), decls, inV1));
		return fun2;
	}

	private static ExprVar getExprVarToSig(ExprVar ev) {
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

	private static Type replaceSigRefs(Type t, boolean inV1) {
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
						throw new RuntimeException("Signature " + pt.get(i).label + " not found in merged signature map.");
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

	private static Sig getInternalSig(String label) {
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

	private static Expr getField(Sig sig, String label) {
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
	private static Expr replaceArrows(Expr expr) {
		switch (expr.getClass().getSimpleName()) {
		case "ExprUnary":
			ExprUnary ue = (ExprUnary) expr;
			return ue.op.make(ue.pos, replaceArrows(ue.sub));
		case "ExprBinary":
			ExprBinary be = (ExprBinary) expr;
			if (be.op.isArrow) {
				return ExprBinary.Op.ARROW.make(be.pos, be.closingBracket, replaceArrows(be.left), replaceArrows(be.right));
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
	private static ExprUnary.Op getMergeOp(ExprUnary.Op op, ExprUnary.Op op2) {
		switch (op) {
		case SETOF:
			return ExprUnary.Op.SETOF;
		case SOMEOF:
			switch (op2) {
			case SETOF:
				return ExprUnary.Op.SETOF;
			case LONEOF:
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
			default:
				// this covers the one operator
				return ExprUnary.Op.ONEOF;
			}
		default:
			return ExprUnary.Op.SETOF;
		}
	}

	private static ExprBinary.Op getArrowForOp(ExprUnary.Op op) {
		switch (op) {
		case ONEOF:
			return ExprBinary.Op.ANY_ARROW_ONE;
		case SOMEOF:
			return ExprBinary.Op.ANY_ARROW_SOME;
		case LONEOF:
			return ExprBinary.Op.ANY_ARROW_LONE;
		default:
			return ExprBinary.Op.ARROW;
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
	private static Expr generateSigAttributeConstraints(Sig s, Sig old, InheritanceUtil iu, Expr c) {
		
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
	private static Attr[] getCommonSigAttributes(Sig s1, Sig s2) {
		List<Attr> attrs = new ArrayList<>();
		for (Attr a1 : s1.attributes) {
			for (Attr a2 : s2.attributes) {
				if (a1 != null && a2 != null && a1.type.equals(a2.type)) {
					attrs.add(new Attr(a1.type, null));
				}
			}
		}
		return attrs.toArray(new Attr[] {});
	}

	/**
	 * a run command taking only new constraints (ignoring any expressions and
	 * scopes)
	 * 
	 * @param v1
	 * @param v2
	 * @return
	 */
	public static Command generateCommand(Module v1, Module v2) {
		Command cmd1 = v1.getAllCommands().get(0);
		Command cmd2 = v2.getAllCommands().get(0);
		

		int overall = Math.max(cmd1.overall, cmd2.overall);
		int bitwidth = Math.max(cmd1.bitwidth, cmd2.bitwidth);
		int maxseq = Math.max(cmd1.maxseq, cmd2.maxseq);

		c1 = c1.and(replaceSigRefs(cmd1.formula, true));
		c2 = c2.and(replaceSigRefs(cmd2.formula, false));
		
		Command cmd = new Command(false, overall, bitwidth, maxseq, c2.and(c1.not()));

		for (Sig s: sigs.values()) {			
			CommandScope s1 = cmd1.getScope(v1Sigs.get(s.label));
			CommandScope s2 = cmd2.getScope(v2Sigs.get(s.label));
						
			int scope = -1;
			boolean exact = false;
			if (s1 != null) {
				scope = Math.max(scope, s1.endingScope);
				exact |= s1.isExact;
			}
			if (s2 != null) {
				scope = Math.max(scope, s2.endingScope);
				exact |= s2.isExact;
			}
			
			if (scope != -1) {
				cmd = cmd.change(s, exact, scope);
			}
			
			if (cmd1.additionalExactScopes.contains(v1Sigs.get(s.label)) ||
					cmd2.additionalExactScopes.contains(v2Sigs.get(s.label))) {
				List<Sig> exactScopes = new ArrayList<>(cmd.additionalExactScopes);
				exactScopes.add(s);				
				cmd = cmd.change(exactScopes.toArray(new Sig[] {}));
			}
		}


//		return new Command(false, -1, -1, -1, c2.and(c1.not()));
		return cmd;
	}
}
