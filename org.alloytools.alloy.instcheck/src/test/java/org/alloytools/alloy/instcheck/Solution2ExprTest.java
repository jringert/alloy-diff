package org.alloytools.alloy.instcheck;

import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import org.alloytools.alloy.instcheck.Solution2Expr;
import org.junit.jupiter.api.Test;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

class Solution2ExprTest {

	private A4Reporter rep = new A4Reporter() {
		@Override
		public void warning(ErrorWarning msg) {
			System.out.print("Relevance Warning:\n" + (msg.toString().trim()) + "\n\n");
			System.out.flush();
		}
	};

	@Test
	void testFlatten() throws Err, IOException {

		String m1file = "../org.alloytools.alloy.diff/misc/inheritance/extends1.als";
		Module m1 = CompUtil.parseEverything_fromFile(rep, null, m1file);
		String m2file = "../org.alloytools.alloy.diff/misc/inheritance/extends1_flattened_direct.als";
		Module m2 = CompUtil.parseEverything_fromFile(rep, null, m2file);

		A4Options options = new A4Options();
		options.solver = A4Options.SatSolver.SAT4J;

		A4Solution ans = TranslateAlloyToKodkod.execute_command(rep, m1.getAllReachableSigs(), m1.getAllCommands().get(0),
				options);

		if (ans.satisfiable()) {
			System.out.println(ans);

			Solution2Expr s2e = new Solution2Expr();
			Expr instExpr = s2e.getExpr(m2, ans);

			Command cmd = m2.getAllCommands().get(0);
			cmd = cmd.change(cmd.formula.and(instExpr));
			System.out.println(cmd.formula);
			List<Sig> sigs = new ArrayList<>(m2.getAllReachableSigs());
			sigs.addAll(s2e.getAtomSigs());
			ans = TranslateAlloyToKodkod.execute_command(rep, sigs, cmd, options);

			assertTrue(ans.satisfiable());

			System.out.println(ans);
		} else {
			fail("original didnt have instances");
		}
	}

}
