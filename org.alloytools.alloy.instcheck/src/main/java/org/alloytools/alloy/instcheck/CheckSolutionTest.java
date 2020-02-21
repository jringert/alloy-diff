package org.alloytools.alloy.instcheck;

import static org.junit.jupiter.api.Assertions.assertTrue;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import org.junit.jupiter.api.Test;

import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

class CheckSolutionTest {

	@Test
	public void ckeckSelfSolutionTest() throws Exception {
		Files.find(Paths.get("../org.alloytools.alloy.diff/misc"), Integer.MAX_VALUE,
				(filePath, fileAttr) -> fileAttr.isRegularFile()).forEach(f -> checkSolutionSelf(f));
	}

	@Test
	public void ckeckSelfSolutionAllAlloyTest() throws Exception {
		Files.find(Paths.get("../org.alloytools.alloy.extra/extra/models"), Integer.MAX_VALUE,
				(filePath, fileAttr) -> fileAttr.isRegularFile()).forEach(f -> checkSolutionSelf(f));
	}

	private void checkSolutionSelf(Path f) {
		if (!f.toString().endsWith(".als")) {
			return;
		}
		System.out.println(f);
		Module m = null;
		try {
			m = CompUtil.parseEverything_fromFile(null, null, f.toString());
		} catch (Exception e) {
			// ignore parsing errors
			return;
		}

		A4Options options = new A4Options();
		options.solver = A4Options.SatSolver.SAT4J;

		A4Solution sol = null;
		try {
			sol = TranslateAlloyToKodkod.execute_command(null, m.getAllReachableSigs(), m.getAllCommands().get(0), options);
		} catch (Exception e) {
			// ignore type errors etc in original specs
			return;
		}

		List<A4Solution> sols = new ArrayList<>();

		// have to calculate in advance otherwise solver has NullPointers when trying to
		// get next solution
		while (sol.satisfiable() && sols.size() < 10) {
			sols.add(sol);
			sol = sol.next();
		}
		for (A4Solution s : sols) {
			System.out.println(s);
			assertTrue(CheckSolution.check(m, s, options));
		}
	}

}
