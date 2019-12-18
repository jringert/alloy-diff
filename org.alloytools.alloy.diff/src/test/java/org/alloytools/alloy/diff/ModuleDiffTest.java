package org.alloytools.alloy.diff;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

import org.junit.Test;

import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.translator.A4Solution;

public class ModuleDiffTest {

	@Test
	public void diffSelfEmptyTest() throws Exception {
		Files.find(Paths.get("misc"), Integer.MAX_VALUE, (filePath, fileAttr) -> fileAttr.isRegularFile())
				.forEach(f -> diffSelfEmpty(f));
	}

	/**
	 * Checks whether the empty module has instances that the current one doesn't.
	 * This could be the case if the current module is unsat by itself (but then the
	 * instances must be empty).
	 * 
	 * @param f
	 */
	private void diffSelfEmpty(Path f) {
		A4Solution ans = ModuleDiff.diff(f.toString(), "misc/empty.als");
		assertTrue(f.toString() + " had a satisfiable diff with empty module", !ans.satisfiable() || size(ans) == 0);
	}

	@Test
	public void diffEmptySelfTest() throws Exception {
		Files.find(Paths.get("misc"), Integer.MAX_VALUE, (filePath, fileAttr) -> fileAttr.isRegularFile())
				.forEach(f -> diffEmptySelf(f));
	}

	/**
	 * Checks whether the current module has instances that the empty module doesn't.
	 * This should be the case. However, it could be that the current module is
	 * sat only for the empty solution.  
	 * 
	 * @param f
	 */
	private void diffEmptySelf(Path f) {
		A4Solution ans = ModuleDiff.diff("misc/empty.als", f.toString());
		
		if (ans.satisfiable()) {
			assertTrue("Empty module had an empty diff with " + f.toString(), size(ans) > 0);	
		} else {
			A4Solution ansF = ModuleDiff.getSolution(f.toString());
			if (ansF.satisfiable()) {
				assertEquals(f.toString(), 0, size(ansF));
				assertFalse(f.toString(), ans.next().satisfiable());
			}			
		}		
	}
	
	private int size(A4Solution ans) {
		int size = 0;
		for (ExprVar v : ans.getAllAtoms()) {
			size++;
		}
		return size;
	}
}
