package org.alloytools.alloy.instcheck;

import static org.junit.jupiter.api.Assertions.assertTrue;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

import org.junit.jupiter.api.Test;

import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

class CheckSolutionTest {

	@Test
	public void ckeckSelfSolutionTest() throws Exception {
		Files.find(Paths.get("../org.alloytools.alloy.diff/misc"), Integer.MAX_VALUE, (filePath, fileAttr) -> fileAttr.isRegularFile())
				.forEach(f -> checkSolutionSelf(f));
	}

	private void checkSolutionSelf(Path f) {
		System.out.println(f);
        Module m = CompUtil.parseEverything_fromFile(null, null, f.toString());
        
        A4Options options = new A4Options();
        options.solver = A4Options.SatSolver.SAT4J;

        A4Solution sol = TranslateAlloyToKodkod.execute_command(null, m.getAllReachableSigs(), m.getAllCommands().get(0), options);
                
        if (sol.satisfiable()) {
        	assertTrue(CheckSolution.check(m, sol));
        }
	}

}
