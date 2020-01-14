package org.alloytools.alloy.diff;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.SafeList;
import edu.mit.csail.sdg.ast.Attr;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprCall;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprHasName;
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

public class ModuleMerger {

	protected static Map<String, Sig> sigs;
	protected static Expr c1;
	protected static Expr c2;

	
	/**
	 * Merges signatures from v1 and v2 by creating combined Sigs for common
	 * signatures and copying unique signatures
	 *
	 * @param v1
	 * @param v2
	 * @return
	 */
	public static Collection<Sig> mergeSigs(Module v1, Module v2) {
		sigs = new HashMap<>();
		Map<String, Sig> v1Sigs = new HashMap<>();
		Map<String, Sig> v2Sigs = new HashMap<>();
		c1 = ExprConstant.TRUE;
		c2 = ExprConstant.TRUE;

		// fill look-up tables
		for (Sig s : v1.getAllSigs()) {
			v1Sigs.put(s.toString(), s);
		}
		for (Sig s : v2.getAllSigs()) {
			v2Sigs.put(s.toString(), s);
		}

		// do merge
		for (String sName : v1Sigs.keySet()) {
			if (v2Sigs.containsKey(sName)) {
				// create a merged signature
				sigs.put(sName, mergeSig(v1Sigs.get(sName), v2Sigs.get(sName)));
			} else {
				// adding signatures that are unique in v1
				Sig s = new PrimSig(sName, v1Sigs.get(sName).attributes.toArray(new Attr[] {}));
				sigs.put(sName, s);
				// closed world
				c2 = c2.and(s.no());
			}
		}
		for (String sName : v2Sigs.keySet()) {
			if (!v1Sigs.containsKey(sName)) {
				// adding signatures that are unique in v2
				Sig s = new PrimSig(sName, v2Sigs.get(sName).attributes.toArray(new Attr[] {}));
				sigs.put(sName, s);
				// closed world
				c1 = c1.and(s.no());
			}
		}

		for (String sName : sigs.keySet()) {
			Sig s = sigs.get(sName);

			Sig s1 = v1Sigs.get(sName);
			Sig s2 = v2Sigs.get(sName);
			if (s1 != null && s2 != null) {
				mergeFields(s, s1.getFields(), s2.getFields());
			} else if (s1 != null) {
				addFields(s, s1.getFields());
			} else {
				addFields(s, s2.getFields());
			}
		}

		return sigs.values();
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
		c1 = generateSigAttributeConstraints(s, s1, c1);
		c2 = generateSigAttributeConstraints(s, s2, c2);

		return s;
	}

	/**
	 *
	 * FIXME: only works for fields of the same arity as a workaround fields with
	 * lower arity could be padded with a singleton signature. However, this would
	 * require changing all expressions on fields.
	 *
	 * FIXME: messes up with field references inside field declarations; check this!
	 *
	 * @param mergedSig
	 * @param fields1
	 * @param fields2
	 */
	private static void mergeFields(Sig mergedSig, SafeList<Field> fields1, SafeList<Field> fields2) {
		Set<Field> unique1 = new HashSet<Sig.Field>();
		Set<Field> unique2 = new HashSet<Sig.Field>();

		for (Field f1 : fields1) {
			unique1.add(f1);
		}
		for (Field f2 : fields2) {
			unique2.add(f2);
		}

		for (Field f1 : fields1) {
			for (Field f2 : fields2) {
				if (f1.label.equals(f2.label)) {
					if (f1.decl().expr instanceof ExprUnary && f2.decl().expr instanceof ExprUnary) {
						ExprUnary e1 = (ExprUnary)replaceSigRefs(f1.decl().expr);
						ExprUnary e2 = (ExprUnary)replaceSigRefs(f2.decl().expr);
						Expr union = e1.sub.plus(e2.sub);
						ExprUnary.Op op = getMergeOp(e1.op, e2.op);
						Field f = mergedSig.addField(f1.label, op.make(f1.pos, union));

						Expr e1mult = getArrowForOp(e1.op).make(f1.pos, f1.closingBracket, mergedSig, e1.sub);
						Expr e2mult = getArrowForOp(e2.op).make(f2.pos, f2.closingBracket, mergedSig, e2.sub);
						c1 = c1.and(f.decl().get().in(e1mult));
						c2 = c2.and(f.decl().get().in(e2mult));

						unique1.remove(f1);
						unique2.remove(f2);
						break;
					} else if (f1.decl().expr instanceof ExprBinary && f2.decl().expr instanceof ExprBinary) {
						Expr e1 = replaceSigRefs(f1.decl().expr);
						Expr e2 = replaceSigRefs(f2.decl().expr);
						Expr union = replaceArrows(e1).plus(replaceArrows(e2));
						Field f = mergedSig.addField(f1.label, union);

						Expr e1mult = ExprBinary.Op.ARROW.make(f1.pos, f1.closingBracket, mergedSig, e1);
						Expr e2mult = ExprBinary.Op.ARROW.make(f2.pos, f2.closingBracket, mergedSig, e2);
						c1 = c1.and(f.decl().get().in(e1mult));
						c2 = c2.and(f.decl().get().in(e2mult));

						unique1.remove(f1);
						unique2.remove(f2);

					} else {
						throw new RuntimeException("Mix of field arities " + f1.pos.filename);
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

	
	private static void addFields(Sig s, SafeList<Field> fields) {
		for (Field f : fields) {
			s.addField(f.label, replaceSigRefs(f.decl().expr));
		}
	}

	private static void addUniqueField(Sig mergedSig, Field field, boolean inC1) {
		Field f;
		Expr e = replaceSigRefs(field.decl().expr);
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
	
	private static List<ExprHasName> replaceSigRefs(ConstList<? extends ExprHasName> es) {
		List<ExprHasName> l = new ArrayList<>();
		for (Expr e : es) {
			l.add((ExprHasName) replaceSigRefs(e));
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
	private static Expr replaceSigRefs(Expr expr) {
		return replaceSigRefs(expr, new ArrayList<>());
	}

	/**
	 * Replaces occurrences of old signatures in the expression by the merged
	 * signatures
	 *
	 * @param expr
	 * @param names list of local names to use for ExprVar
	 * @return
	 */
	private static Expr replaceSigRefs(Expr expr, List<Decl> names) {
		switch (expr.getClass().getSimpleName()) {
		case "ExprUnary":
			ExprUnary ue = (ExprUnary) expr;
			return ue.op.make(ue.pos, replaceSigRefs(ue.sub, names));
		case "ExprBinary":
			ExprBinary be = (ExprBinary) expr;
			return be.op.make(be.pos, be.closingBracket, replaceSigRefs(be.left, names), replaceSigRefs(be.right, names));
		case "PrimSig":
			PrimSig ps = (PrimSig) expr;
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
				l.add(replaceSigRefs(e, names));
			}
			return ExprList.make(el.pos, el.closingBracket, Op.AND, l);
		case "ExprQt":
			ExprQt eq = (ExprQt) expr;
			List<Decl> decls = new ArrayList<Decl>();
			for (Decl d : eq.decls) {
				decls.add(new Decl(d.isPrivate, d.disjoint, d.disjoint2, replaceSigRefs(d.names),
						replaceSigRefs(d.expr, names)));
			}
			return eq.op.make(eq.pos, eq.closingBracket, decls, replaceSigRefs(eq.sub, decls));
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
			ExprVar ret = ExprVar.make(ev.pos, ev.label, replaceSigRefs(t));
			return ret;
		case "Field":
			Field f = (Field) expr;
			return getField(sigs.get(f.sig.label), f.label);
		case "ExprConstant":
			return expr;
		case "ExprCall":
			ExprCall ec = (ExprCall) expr;
			List<Expr> args = new ArrayList<>();
			for (Expr c : ec.args) {
				args.add(replaceSigRefs(c, names));
			}
			Expr nec = ExprCall.make(ec.pos, ec.closingBracket, replaceSigRefs(ec.fun), args, 0);
			return nec;
		default:
			System.out.println(expr.getClass().getSimpleName());
			throw new RuntimeException(
					"Error in replaceSigRefs for: " + expr.getClass().getSimpleName() + "\nat " + expr.pos);
		}
	}

	private static Func replaceSigRefs(Func fun) {
		List<Decl> decls = new ArrayList<Decl>();
		for (Decl d : fun.decls) {
			decls.add(new Decl(d.isPrivate, d.disjoint, d.disjoint2, replaceSigRefs(d.names),
					replaceSigRefs(d.expr)));
		}
		Func fun2 = new Func(fun.pos, fun.label, decls, replaceSigRefs(fun.returnDecl, decls),
				replaceSigRefs(fun.getBody(), decls));
		return fun2;
	}

	private static Type replaceSigRefs(Type t) {
		for (ProductType pt : t) {
			if (pt.arity() != 1) {
				throw new RuntimeException("Ecountered type with arity != 1");
			}
			for (int i = 0; i < pt.arity(); i++) {
				Sig s = sigs.get(pt.get(i).label);
				if (s == null) {
					s = getInternalSig(pt.get(i).label);
					if (s == null) {
						throw new RuntimeException(
								"Signature " + pt.get(i).label + " not found in merged signature map.");
					}
				}
				return s.type();
			}
		}
		throw new RuntimeException("Unhandled case at end of replaceSigRefs(Type t)");
	}

	private static Sig getInternalSig(String label) {
		switch (label) {
		case "univ":
			sigs.put(label, Sig.UNIV);
			return Sig.UNIV;
		case "Int":
			sigs.put(label, Sig.SIGINT);
			return Sig.SIGINT;
		case "seq/Int":
			sigs.put(label, Sig.SEQIDX);
			return Sig.SEQIDX;
		case "String":
			sigs.put(label, Sig.STRING);
			return Sig.STRING;
		case "none":
			sigs.put(label, Sig.NONE);
			return Sig.NONE;
		default:
			return null;
		}

	}

	private static Expr getField(Sig sig, String label) {
		for (Field f : sig.getFields()) {
			if (f.label.equals(label)) {
				return f;
			}
		}
		return null;
	}



	/**
	 * replaces any arrow inside binary expressions by the default arrow "->"
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
				return ExprBinary.Op.ARROW.make(be.pos, be.closingBracket, replaceArrows(be.left),
						replaceArrows(be.right));
			} else {
				return be.op.make(be.pos, be.closingBracket, replaceArrows(be.left), replaceArrows(be.right));
			}
		case "PrimSig":
			PrimSig ps = (PrimSig) expr;
			return sigs.get(ps.label);
		case "ExprList":
			ExprList el = (ExprList) expr;
			List<Expr> l = new ArrayList<Expr>();
			for (Expr e : el.args) {
				l.add(replaceArrows(e));
			}
			return ExprList.make(el.pos, el.closingBracket, Op.AND, l);
		case "Field":
			Field f = (Field) expr;
			return getField(sigs.get(f.sig.label), f.label);
		default:
			throw new RuntimeException("replaceArrows(..) unhandled expr: " + expr.getClass().getSimpleName());
		}
	}

	/**
	 * FIXME Should implement the table!
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
	private static Expr generateSigAttributeConstraints(Sig s, Sig old, Expr c) {
		if (old.isAbstract != null && s.isAbstract == null) {
			//without inheritence, abstract has no impact
			//c = c.and(s.no()); 
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
	 * keep all common attributes
	 * FIXME for multiplicities is should be better to take the least upper bound 
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

	public static void mergeCommands(Command cmd1, Command cmd2) {
		c1 = c1.and(replaceSigRefs(cmd1.formula));
		c2 = c2.and(replaceSigRefs(cmd2.formula));
	}

	public static Command generateCommand(Module v1, Module v2) {
		ModuleMerger.mergeCommands(v1.getAllCommands().get(0), v2.getAllCommands().get(0));

		return new Command(false, -1, -1, -1, c2.and(c1.not()));
	}
}
