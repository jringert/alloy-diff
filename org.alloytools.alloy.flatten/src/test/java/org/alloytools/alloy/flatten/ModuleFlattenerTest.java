package org.alloytools.alloy.flatten;

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

class ModuleFlattenerTest {
	
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
        Module m = CompUtil.parseEverything_fromFile(rep, null, m1file);
        
        Module mFlat = ModuleFlattener.flatten(m);
        
        A4Options options = new A4Options();
        options.solver = A4Options.SatSolver.SAT4J;

        A4Solution ans = TranslateAlloyToKodkod.execute_command(rep, m.getAllReachableSigs(), m.getAllCommands().get(0), options);
        
        if (ans.satisfiable()) {
        	Solution2Expr s2e = new Solution2Expr();
        	Expr instExpr = s2e.getExpr(mFlat, ans);
        	
        	Command cmd = mFlat.getAllCommands().get(0);
        	cmd = cmd.change(cmd.formula.and(instExpr));
        	
        	List<Sig> sigs = new ArrayList<>(mFlat.getAllReachableSigs());
        	sigs.addAll(s2e.getAtomSigs());
        	ans = TranslateAlloyToKodkod.execute_command(rep, sigs, cmd, options);
        	
        	assertTrue(ans.satisfiable());          
        } else {
        	fail("original didnt have instances");
        }
	}

}
