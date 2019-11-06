package org.alloytools.alloy.diff;

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
import edu.mit.csail.sdg.ast.Expr;
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

		Module v1 = CompUtil.parseEverything_fromFile(rep, null, "misc/multiplicities/b1.als");
		Module v2 = CompUtil.parseEverything_fromFile(rep, null, "misc/multiplicities/b2.als");

		// Choose some default options for how you want to execute the
		// commands
		A4Options options = new A4Options();

		options.solver = A4Options.SatSolver.SAT4J;

		c1 = Sig.UNIV.equal(Sig.UNIV);
		c2 = Sig.UNIV.equal(Sig.UNIV);
		Collection<Sig> sigs = mergeSigs(v1, v2);

		Command diffCommand = new Command(false, -1, -1, -1, c2.and(c1.not()));

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
	private static Collection<Sig> mergeSigs(Module v1, Module v2) {
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
				sigs.put(sName, v1Sigs.get(sName));
			}
		}
		for (String sName : v2Sigs.keySet()) {
			if (!v1Sigs.containsKey(sName)) {
				// adding signatures that are unique in v2
				sigs.put(sName, v2Sigs.get(sName));
			}
		}

		return sigs.values();
	}

	
	/**
	 * Creates a merged signature and adds constraints c1 c2 for individual sigs
	 * @param s1
	 * @param s2
	 * @return
	 */
	private static Sig mergeSig(Sig s1, Sig s2) {
		Sig s = new PrimSig(s1.label, getCommonSigAttributes(s1, s2));		
		c1 = generateSigAttributeConstraints(s, s1, c1);
		c2 = generateSigAttributeConstraints(s, s2, c2);
		
		//s1.getFieldDecls();
		SafeList<Field> fields1 = s1.getFields();
		SafeList<Field> fields2 = s2.getFields();
		
		SafeList<Field> mergedFields = mergeFields(fields1, fields2);
		for (Field f : mergedFields) {
			ExprUnary exp = (ExprUnary) f.decl().expr;
			System.out.println(exp.op == Op.LONEOF);
		}
		
		return s;
	}

	private static SafeList<Field> mergeFields(SafeList<Field> fields1, SafeList<Field> fields2) {
		SafeList<Field> fields = new SafeList<Sig.Field>();
		for (Field field1 : fields1) {
			for (Field field2 : fields2) {
				ExprUnary expField1 = (ExprUnary) field1.decl().expr;
				ExprUnary expField2 = (ExprUnary) field2.decl().expr;
				if (field1.decl().names[0].label == field2.decl().names[0].label) {
					
				}
			}
		}
		return fields;
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

}
