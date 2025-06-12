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
import edu.mit.csail.sdg.translator.A4Options.SatSolver;

public class ModuleDiff {

	public static SatSolver solver = null;
	
	public static int totalVarsSAT = 0;

	public static void main(String[] args) {
		if (args.length < 2) {
			System.out.println("Usage: ModuleDiff <leftFile> <rightFile> [analysis:SemDiff|CommonInst|Equivalence] [scope] [withPred] [solver:sat4j|cryptoMinisat|minisat]");
			return;
		}
		String leftFile = args[0];
		String rightFile = args[1];
		int scope = -1;
		boolean withPred = true;

		Analysis analysis = Analysis.SemDiff; // default analysis
		if (args.length >= 3 && args[2] != null && !args[2].isEmpty()) {
			analysis = Analysis.valueOf(args[2]);
			if (analysis == null) {
				System.out.println("Unknown analysis: " + args[2]);
				return;
			}
		} else {
			System.out.println("Using default analysis: " + analysis);
		}

		if (args.length >= 4) {
			scope = Integer.parseInt(args[3]);
		} else {
			System.out.println("Using default scope: " + scope);
		}

		if (args.length >= 5) {
			withPred = Boolean.parseBoolean(args[4]);
		} else {
			System.out.println("Using default withPred: " + withPred);
		}

		if (args.length >= 6) {
			String solverName = args[5].toLowerCase();
			if (solverName.equals("sat4j")) {
				solver = SatSolver.SAT4J;
			} else if (solverName.equals("cryptominisat")) {
				solver = SatSolver.CryptoMiniSatJNI;
			} else if (solverName.equals("minisat")) {
				solver = SatSolver.MiniSatJNI;
			} else {
				System.out.println("Unknown solver: " + solverName);
				return;
			}
		} else {
			System.out.println("Using default solver: " + solver);
		}

		A4Solution solution = diff(leftFile, rightFile, scope, withPred, analysis);
		switch (analysis) {
			case SemDiff:
				if (!solution.satisfiable()) {
					System.out.println("The two modules are equivalent for the given scope.");
				} else {
					System.out.println("Diff result: \n" + solution);
				}
				break;
			case CommonInst:
				if (!solution.satisfiable()) {
					System.out.println("There are no common instances for the two modules and this scope.");
				} else {
					System.out.println("Common instances found: \n" + solution);
				}
				break;
			case Equivalence:
				System.out.println("Equivalence result: " + solution);
				if (!solution.satisfiable()) {
					System.out.println("The two modules are equivalent.");
				} else {
					System.out.println("The two modules are not equivalent.");
					System.out.println("Diff result: \n" + solution);
				}
				break;
		
			default:
				break;
		}
	}


	public static A4Reporter rep = new A4Reporter() {
		private boolean quiet = true;
		

		@Override
		public void bound(String msg) {
			if (!quiet) {
				System.out.println(msg);
				System.out.flush();
			}
			super.bound(msg);
		}

		@Override
		public void debug(String msg) {
			if (!quiet) {
				System.out.println(msg);
				System.out.flush();
			}
			super.debug(msg);
		}

		@Override
		public void warning(ErrorWarning msg) {
			if (!quiet) {
				System.out.println("Relevance Warning:\n" + (msg.toString().trim()) + "\n\n");
				System.out.flush();
			}
		}

		@Override
		public void solve(int primaryVars, int totalVars, int clauses) {
			totalVarsSAT = totalVars;
//			if (!quiet) {
				System.out.println(totalVars + " vars. " + primaryVars + " primary vars. " + clauses + " clauses.");
				System.out.flush();
//			}
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
				System.out.println("bitwidth " + bitwidth + " skolemDepth " + skolemDepth);
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
	public static A4Solution diff(String leftFile, String rightFile, int scope, boolean withPred, Analysis a) {

		Module v1, v2;

		try {
			v1 = CompUtil.parseEverything_fromFile(rep, null, leftFile);
			v2 = CompUtil.parseEverything_fromFile(rep, null, rightFile);
		} catch (Exception e) {
			throw new RuntimeException("Alloy failed to parse module.", e);
		}

		return diff(v1, v2, scope, withPred, a);
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
	private static A4Solution diff(Module v1, Module v2, int scope, boolean withPred, Analysis a) {

		options.skolemDepth = 1;
		if (solver != null) {
			options.solver = solver;
		} else if (System.getProperty("os.name").contains("indows")) {
			options.solver = A4Options.SatSolver.SAT4J;
		} else {
			options.solver = A4Options.SatSolver.CryptoMiniSatJNI;
		}

		ModuleMerger m = new ModuleMerger();
		Collection<Sig> sigs = m.mergeSigs(v1, v2);

		CommandGenerator cg = new CommandGenerator(m);
		Command diffCommand = cg.generateDiffCommand(v1, v2, scope, withPred, a);			

		A4Solution ans = TranslateAlloyToKodkod.execute_command(rep, sigs, diffCommand, options);

		return ans;
	}

	public static A4Solution getSolution(String fileName) {
		Module v1 = CompUtil.parseEverything_fromFile(rep, null, fileName);
		A4Solution ans = TranslateAlloyToKodkod.execute_command(rep, v1.getAllReachableSigs(), v1.getAllCommands().get(0),
				options);
		return ans;
	}

	public static A4Solution diff(String leftFile, String rightFile, int scope, boolean withPred) {
		return diff(leftFile, rightFile, scope, withPred, Analysis.SemDiff);
	}
}
