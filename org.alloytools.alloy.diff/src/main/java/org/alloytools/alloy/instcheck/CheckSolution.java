package org.alloytools.alloy.instcheck;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

public class CheckSolution {

	public static boolean check(Collection<Sig> sigs, Command cmd, A4Solution sol) {
		A4Options options = new A4Options();
		options.solver = A4Options.SatSolver.SAT4J;

		return check(sigs, cmd, sol, options);
	}

	/**
	 * checks whether the solution is a solution for the first run command of the
	 * provided module
	 * 
	 * @param m
	 * @param sol
	 * @return
	 */
	public static boolean check(Collection<Sig> sigs, Command cmd, A4Solution sol, A4Options options) {
		if (sol.satisfiable()) {
			Solution2Expr s2e = new Solution2Expr();
			Expr instExpr = s2e.getExpr(sigs, sol);

			cmd = cmd.change(cmd.formula.and(instExpr));

			List<Sig> newSigs = new ArrayList<>();
			newSigs.addAll(sigs);
			newSigs.addAll(s2e.getAtomSigs());

			sol = TranslateAlloyToKodkod.execute_command(null, newSigs, cmd, options);

			return sol.satisfiable();
		}
		return false;
	}
}
