package org.alloytools.alloy.diff;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.stream.Stream;

import org.junit.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.ErrorType;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Solution;

public class ModuleDiffTest {	
	
	static String[] sigFolders = new String[] { "misc", "../models-master", "../iAlloy-dataset-master", "../platinum-experiment-data/" };
//	static String[] sigFolders = new String[] { "misc/fields/fields2.als" };
//	static String[] sigFolders = new String[] { "misc/quantification/q2.als" };
//	static String[] sigFolders = new String[] { "../models-master/puzzles/einstein/einstein-wikipedia.als"};

	/**
	 * Checks whether the empty module has instances that the current one doesn't.
	 * This could be the case if the current module is unsat by itself (but then the
	 * instances must be empty).
	 * 
	 * @param f
	 */
	@ParameterizedTest
	@MethodSource("allAlloyFiles")
	public void diffSelfEmpty(Path f) {
		System.out.println("diff " + f.toString() + " and empty.als");
		try {
			A4Solution ans = ModuleDiff.diff(f.toString(), "misc/empty.als");
			assertTrue(f.toString() + " had a satisfiable diff with empty module", !ans.satisfiable() || size(ans) == 0);
		} catch (ErrorType e) {
			if (e.getMessage().contains("higher-order")) {
				System.out.println(e.getMessage());
			} else {
				throw e;
			}
		}
	}

	public static Stream<Arguments> allAlloyFiles() throws Exception {
		Stream<Arguments> allFiles = null;
		for (String folder : sigFolders) {
			Stream<Arguments> inThisFolder = 
			Files
					.find(Paths.get(folder), Integer.MAX_VALUE,
							(filePath, fileAttr) -> fileAttr.isRegularFile() && filePath.toString().endsWith(".als")).map(f -> Arguments.of(f));
			if (allFiles == null) {
				allFiles = inThisFolder;
			} else {
				allFiles = Stream.concat(allFiles, inThisFolder);
			}
		}
		return allFiles;
	}

	/**
	 * Checks whether the current module has instances that the empty module
	 * doesn't. This should be the case. However, it could be that the current
	 * module is sat only for the empty solution.
	 * 
	 * @param f
	 */
	@ParameterizedTest
	@MethodSource("allAlloyFiles")
	public void diffEmptySelf(Path f) {
		System.out.println("diff empty.als and " + f.toString());
		A4Solution ans = null;
		try {
			ans = ModuleDiff.diff("misc/empty.als", f.toString());
		} catch (ErrorSyntax e) {
			if (e.getMessage().contains("File cannot be found")) {
				return;
			} else {
				throw e;
			}
		}
		
		if (ans.satisfiable()) {
			assertTrue("Empty module had an empty diff with " + f.toString(), size(ans) > 0);
		} else {
			A4Solution ansF = ModuleDiff.getSolution(f.toString());
			if (ansF.satisfiable() && !CompUtil.parseEverything_fromFile(null, null, f.toString()).getAllCommands().get(0).check) {
				assertEquals(f.toString(), 0, size(ansF));
				assertFalse(f.toString(), ans.next().satisfiable());
			}
		}
	}

	private int size(A4Solution ans) {
		int size = 0;
		for (ExprVar v : ans.getAllAtoms()) {
			Sig as = v.type().iterator().next().get(0);
			if (as.toString().startsWith("this")) {
				size++;
			}
		}
		return size;
	}
	
	@Test
	public void diffExtends12() {
		A4Solution ans = ModuleDiff.diff("misc/inheritance/extends1v1.als", "misc/inheritance/extends1v2.als");
		assertFalse(ans.satisfiable());

		ans = ModuleDiff.diff("misc/inheritance/extends1v2.als", "misc/inheritance/extends1v1.als");
		assertFalse(ans.satisfiable());
	}
	
	@Test
	public void diffExtends13() {
		A4Solution ans = ModuleDiff.diff("misc/inheritance/extends1v1.als", "misc/inheritance/extends1v3.als");
		assertTrue(ans.satisfiable());

		ans = ModuleDiff.diff("misc/inheritance/extends1v3.als", "misc/inheritance/extends1v1.als");
		assertTrue(ans.satisfiable());
	}
	
	@Test
	public void diffExtends23() {
		A4Solution ans = ModuleDiff.diff("misc/inheritance/extends1v2.als", "misc/inheritance/extends1v3.als");
		assertTrue(ans.satisfiable());

		ans = ModuleDiff.diff("misc/inheritance/extends1v3.als", "misc/inheritance/extends1v2.als");
		assertTrue(ans.satisfiable());
	}
	
	@Test
	public void diffFacts12() {
		A4Solution ans = ModuleDiff.diff("misc/facts/factV1.als", "misc/facts/factV2.als");
		assertFalse(ans.satisfiable());

		ans = ModuleDiff.diff("misc/facts/factV2.als", "misc/facts/factV1.als");
		assertTrue(ans.satisfiable());
		System.out.println(ans);
	}
}
