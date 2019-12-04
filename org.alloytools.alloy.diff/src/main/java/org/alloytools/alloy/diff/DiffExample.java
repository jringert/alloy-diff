package org.alloytools.alloy.diff;

import java.util.Collection;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4viz.VizGUI;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
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

//		Module v1 = CompUtil.parseEverything_fromFile(rep, null, "misc/multiplicities/oneBank.als");
//		Module v2 = CompUtil.parseEverything_fromFile(rep, null, "misc/multiplicities/Bank.als");

		Module v2 = CompUtil.parseEverything_fromFile(rep, null, "misc/File1.als");
		Module v1 = CompUtil.parseEverything_fromFile(rep, null, "misc/File2.als");

		// Choose some default options for how you want to execute the
		// commands
		A4Options options = new A4Options();

		options.solver = A4Options.SatSolver.SAT4J;

		
		ModuleMerger m = new ModuleMerger();
		Collection<Sig> sigs = m.mergeSigs(v1, v2);
		m.mergeCommands(v1.getAllCommands().get(0), v2.getAllCommands().get(0));
		
		

		System.out.println(m.c1);
		System.out.println(m.c2);
		Command diffCommand = new Command(false, -1, -1, -1, m.c2.and(m.c1.not()));
		
//		Command diffCommand = new Command(false, -1, -1, -1, ExprConstant.TRUE);

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


}
