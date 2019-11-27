package org.alloytools.alloy.diff;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.fail;

import java.io.File;
import java.io.IOException;
import java.io.ObjectInputStream.GetField;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.SafeList;
import edu.mit.csail.sdg.alloy4viz.VizGUI;
import edu.mit.csail.sdg.ast.Attr;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprUnary.Op;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.ast.Sig.PrimSig;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

import org.junit.jupiter.api.Test;

/**
 * This class demonstrates how to access Alloy4 via the compiler methods.
 */

public final class DiffExample {

	public static void main(String[] args) throws Err {

		VizGUI viz = null;

		A4Reporter rep = new A4Reporter() {
			@Override
			public void warning(ErrorWarning msg) {
				System.out.print("Relevance Warning:\n" + (msg.toString().trim()) + "\n\n");
				System.out.flush();
			}
		};

		Module v1 = CompUtil.parseEverything_fromFile(rep, null, "misc/multiplicities/testSignatureCountv1.als");
		Module v2 = CompUtil.parseEverything_fromFile(rep, null, "misc/multiplicities/testSignatureCountv2.als");

		// Choose some default options for how you want to execute the
		// commands
		A4Options options = new A4Options();

		options.solver = A4Options.SatSolver.SAT4J;

		c1 = Sig.UNIV.equal(Sig.UNIV);
		c2 = Sig.UNIV.equal(Sig.UNIV);
		Collection<Sig> sigs = mergeSigs(v1, v2);

//		Command diffCommand = new Command(false, -1, -1, -1, c2.and(c1.not()));
		Command diffCommand = new Command(false, -1, -1, -1, Sig.UNIV.equal(Sig.UNIV));

		// Execute the command
		System.out.println("============ Command " + diffCommand + ": ============");
		A4Solution ans = TranslateAlloyToKodkod.execute_command(rep, sigs, diffCommand, options);

		// Print the outcome
		System.out.println(ans);
		// If satisfiable...
		if (ans.satisfiable()) {
			// You can query "ans" to find out the values of each set or
			// type.
			// This can be useful for debugging.
			//
			// You can also write the outcome to an XML file
			ans.writeXML("alloy_example_output.xml");
			//
			// You can then visualize the XML file by calling this:
			if (viz == null) {
				viz = new VizGUI(false, "alloy_example_output.xml", null);
			}
		}

	}

	private static Map<String, Sig> sigs;
	private static Expr c1;
	private static Expr c2;

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

	private static void addFields(Sig s, SafeList<Field> fields) {
		for (Field f : fields) {
			s.addField(f.label, replaceSigRefs(f.decl().expr));
		}
	}

	/**
	 * Replaces occurrences of old signatures in the expression by the merged
	 * signatures
	 * 
	 * @param expr
	 * @return
	 */
	private static Expr replaceSigRefs(Expr expr) {
		switch (expr.getClass().getSimpleName()) {
		case "ExprUnary":
			ExprUnary ue = (ExprUnary) expr;
			return ue.op.make(ue.pos, replaceSigRefs(ue.sub));
		case "ExprBinary":
			ExprBinary be = (ExprBinary) expr;
			return be.op.make(be.pos, be.closingBracket, replaceSigRefs(be.left), replaceSigRefs(be.right));
		case "PrimSig":
			PrimSig ps = (PrimSig) expr;
			return sigs.get(ps.label);
		default:
			System.err.println(expr.getClass().getSimpleName());
			break;
		}
		return null;
	}

	/**
	 * Sets a field of the object to the new value (using reflection)
	 * 
	 * @param o
	 * @param fieldName
	 * @param updated
	 */
	private static void set(Object o, String fieldName, Expr updated) {
		java.lang.reflect.Field f = null;
		try {
			f = o.getClass().getDeclaredField(fieldName);
			f.setAccessible(true);
			f.set(o, updated);
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
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
		c1 = generateSigAttributeConstraints(s, s1, c1);
		c2 = generateSigAttributeConstraints(s, s2, c2);

		return s;
	}

	/**
	 * TODO this method doesn't work if there are no fields in either signature
	 * versions
	 * 
	 * @param mergedSig
	 * @param fields1
	 * @param fields2
	 */

	private static void mergeFields(Sig mergedSig, SafeList<Field> fields1, SafeList<Field> fields2) {

		for (Field field1 : fields1) {
			for (Field field2 : fields2) {
				ExprUnary expField1 = (ExprUnary) replaceSigRefs(field1.decl().expr);
				ExprUnary expField2 = (ExprUnary) replaceSigRefs(field2.decl().expr);
				if (field1.label.equals(field2.label)) {
					Expr union = expField1.sub.plus(expField2.sub);
					Field f;
					// names are same and type is same but the operator is not same
					switch (expField1.op) {
					case SETOF:
						mergedSig.addField(field1.label, union.setOf());
						break;
					case SOMEOF:
						switch (expField2.op) {
						case SETOF:
							f = mergedSig.addField(field1.label, union.setOf());
							// all s : mergedSig | some s.field
							c1.and(f.some());
							break;
						case LONEOF:
							f = mergedSig.addField(field1.label, union.setOf());
							c1.and(f.some());
							c2.and(f.lone());
							break;
						default:
							// this covers both the some and the one operator
							mergedSig.addField(field1.label, union.someOf());
							break;
						}
						break;
					case LONEOF:
						switch (expField2.op) {
						case SETOF:
							mergedSig.addField(field1.label, union.setOf());
							break;
						case SOMEOF:
							mergedSig.addField(field1.label, union.setOf());
							break;
						default:
							// this covers both the lone and the one operator
							mergedSig.addField(field1.label, union.loneOf());
							break;
						}
						break;
					case ONEOF:
						switch (expField2.op) {
						case SETOF:
							mergedSig.addField(field1.label, union.setOf());
							break;
						case SOMEOF:
							mergedSig.addField(field1.label, union.someOf());
							break;
						case LONEOF:
							mergedSig.addField(field1.label, union.loneOf());
							break;
						default:
							// this covers the one operator
							mergedSig.addField(field1.label, union.oneOf());
							break;
						}
						break;
					default:
						break;
					}
				} else {
					// the field names don't match
					// adding field1
					switch (expField1.op) {
					case ONEOF:
						mergedSig.addField(field1.label, expField1.sub.loneOf());
						break;
					case SOMEOF:
						mergedSig.addField(field1.label, expField1.sub.setOf());
						break;
					default:
						// this handles both set and lone
						mergedSig.addField(field1.label, expField1.sub);
						break;
					}

					// adding field2
					switch (expField2.op) {
					case ONEOF:
						mergedSig.addField(field2.label, expField2.sub.loneOf());
						break;
					case SOMEOF:
						mergedSig.addField(field2.label, expField2.sub.setOf());
						break;
					default:
						// this handles both set and lone
						mergedSig.addField(field2.label, expField2.sub);
						break;
					}
				}
			}
		}

	}

	/**
	 * create constraints for attributes
	 * 
	 * FIXME add the additional attributes
	 * 
	 * @param s
	 * @param old
	 * @param c
	 * @return
	 */
	private static Expr generateSigAttributeConstraints(Sig s, Sig old, Expr c) {
		if (old.isAbstract != null && s.isAbstract == null) {
			c = c.and(s.no());
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

	@Test
	/**
	 * tests if two modules signature counts have changed when they are not supposed to change
	 * Ex. If both modules have signature names that do not match then, then the merged module should have 
	 * 		all signatures
	 */
	void testSignatureCountV1() {
		A4Reporter rep = new A4Reporter() {
			@Override
			public void warning(ErrorWarning msg) {
				System.out.print("Relevance Warning:\n" + (msg.toString().trim()) + "\n\n");
				System.out.flush();
			}
		};
		c1 = Sig.UNIV.equal(Sig.UNIV);
		c2 = Sig.UNIV.equal(Sig.UNIV);
		Module v1 = CompUtil.parseEverything_fromFile(rep, null, "misc/multiplicities/testSignatureCountv1.als");
		Module v2 = CompUtil.parseEverything_fromFile(rep, null, "misc/multiplicities/testSignatureCountv2.als");

		int v1SigsCount = v1.getAllSigs().size();
		int v2SigsCount = v1.getAllSigs().size();

		Collection<Sig> sigs = mergeSigs(v1, v2);

		assertEquals(v1SigsCount + v2SigsCount, sigs.size());
	}
	
	@Test
	/**
	 * tests if two modules signature counts have changed as needed
	 * Ex. If module 1 has 2 signatures and module 2 has 2 signatures, and 1 signature name is common between both,
	 * 		then the merged module should have 3 signatures
	 */
	void testSignatureCountV2() {
		A4Reporter rep = new A4Reporter() {
			@Override
			public void warning(ErrorWarning msg) {
				System.out.print("Relevance Warning:\n" + (msg.toString().trim()) + "\n\n");
				System.out.flush();
			}
		};
		c1 = Sig.UNIV.equal(Sig.UNIV);
		c2 = Sig.UNIV.equal(Sig.UNIV);
		Module v1 = CompUtil.parseEverything_fromFile(rep, null, "misc/multiplicities/testSignatureCountv1.als");
		Module v2 = CompUtil.parseEverything_fromFile(rep, null, "misc/multiplicities/testSignatureCountv2.als");

		int v1SigsCount = v1.getAllSigs().size();
		int v2SigsCount = v1.getAllSigs().size();

		Collection<Sig> sigs = mergeSigs(v1, v2);

		assertEquals(v1SigsCount + v2SigsCount, sigs.size());
	}
	
}
