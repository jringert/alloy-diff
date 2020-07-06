package org.alloytools.alloy.diff;

import java.util.Collection;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

public class ModuleDiff {
	public static int totalVarsSAT = 0;

	public static A4Reporter rep = new A4Reporter() {
		private boolean quiet = false;
		

		@Override
		public void bound(String msg) {
			if (!quiet) {
				System.out.print(msg);
				System.out.flush();
			}
			super.bound(msg);
		}

		@Override
		public void debug(String msg) {
			if (!quiet) {
				System.out.print(msg);
				System.out.flush();
			}
			super.debug(msg);
		}

		@Override
		public void warning(ErrorWarning msg) {
			if (!quiet) {
				System.out.print("Relevance Warning:\n" + (msg.toString().trim()) + "\n\n");
				System.out.flush();
			}
		}

		@Override
		public void solve(int primaryVars, int totalVars, int clauses) {
			totalVarsSAT = totalVars;
			if (!quiet) {
				System.out.print(totalVars + " vars. " + primaryVars + " primary vars. " + clauses + " clauses.");
				System.out.flush();
			}
			super.solve(primaryVars, totalVars, clauses);
		}

//		@Override
//		public void typecheck(String msg) {
//			if (!quiet) {
//				System.out.print(msg);
//				System.out.flush();
//			}
//		}

		@Override
		public void translate(String solver, int bitwidth, int maxseq, int skolemDepth, int symmetry) {
			if (!quiet) {
				System.out.print("bitwidth " + bitwidth + " skolemDepth " + skolemDepth);
				System.out.flush();
			}
		}
	};

	public static A4Options options = new A4Options();

	/**
	 * instances of rightFile that are not instances of left file
	 * 
	 * @param leftFile
	 * @param rightFile
	 * @return
	 */
	public static A4Solution diff(String leftFile, String rightFile, int scope, boolean withPred) {

		Module v1, v2;

		v1 = CompUtil.parseEverything_fromFile(rep, null, leftFile);
		v2 = CompUtil.parseEverything_fromFile(rep, null, rightFile);

		return diff(v1, v2, scope, withPred);
	}
	
	public static A4Solution diff(String leftFile, String rightFile, boolean withPred) {
		return diff(leftFile, rightFile, -1, withPred);
	}
	public static A4Solution diff(String leftFile, String rightFile) {
		return diff(leftFile, rightFile, -1, true);
	}


	/**
	 * Generate a diff (v2 and not v1) as A4Solution.
	 * 
	 * @param v1
	 * @param v2
	 * @return
	 */
	private static A4Solution diff(Module v1, Module v2, int scope, boolean withPred) {

		if (System.getProperty("os.name").contains("indows")) {
			options.solver = A4Options.SatSolver.SAT4J;
		} else {
			options.solver = A4Options.SatSolver.CryptoMiniSatJNI;
		}

		ModuleMerger m = new ModuleMerger();
		Collection<Sig> sigs = m.mergeSigs(v1, v2);

		CommandGenerator cg = new CommandGenerator(m);
		Command diffCommand;
		if (withPred) {
			diffCommand = cg.generatePredDiffCommand(v1, v2, scope);			
		} else {
			diffCommand = cg.generatePlainDiffCommand(v1, v2, scope);
		}

		A4Solution ans = TranslateAlloyToKodkod.execute_command(rep, sigs, diffCommand, options);

		return ans;
	}

	public static A4Solution getSolution(String fileName) {
		Module v1 = CompUtil.parseEverything_fromFile(rep, null, fileName);
		A4Solution ans = TranslateAlloyToKodkod.execute_command(rep, v1.getAllReachableSigs(), v1.getAllCommands().get(0),
				options);
		return ans;
	}
}
