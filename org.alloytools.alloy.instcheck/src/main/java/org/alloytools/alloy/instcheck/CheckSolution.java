package org.alloytools.alloy.instcheck;

import java.util.ArrayList;
import java.util.List;

import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

public class CheckSolution {

	public static boolean check(Module m, A4Solution sol) {
		A4Options options = new A4Options();
		options.solver = A4Options.SatSolver.SAT4J;

		return check(m, sol, options);
	}

	/**
	 * checks whether the solution is a solution for the first run command of the
	 * provided module
	 * 
	 * @param m
	 * @param sol
	 * @return
	 */
	public static boolean check(Module m, A4Solution sol, A4Options options) {
		if (sol.satisfiable()) {
			Solution2Expr s2e = new Solution2Expr();
			Expr instExpr = s2e.getExpr(m, sol);

			Command cmd = m.getAllCommands().get(0);
			cmd = cmd.change(cmd.formula.and(instExpr));

			List<Sig> sigs = new ArrayList<>(m.getAllReachableSigs());
			sigs.addAll(s2e.getAtomSigs());

			sol = TranslateAlloyToKodkod.execute_command(null, sigs, cmd, options);

			return sol.satisfiable();
		}
		return false;
	}
}
