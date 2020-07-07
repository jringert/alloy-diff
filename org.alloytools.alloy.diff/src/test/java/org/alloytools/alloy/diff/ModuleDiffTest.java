package org.alloytools.alloy.diff;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.stream.Stream;

import org.junit.Ignore;
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

	static String[] sigFolders = new String[] { "misc", "../models-master", "../iAlloy-dataset-master",
			"../platinum-experiment-data/" };
//	static String[] sigFolders = new String[] { "misc/fields/fields1.als" };
//	static String[] sigFolders = new String[] { "../platinum-experiment-data/"};
//	static String[] sigFolders = new String[] { "misc/quantification/q2.als" };
//	static String[] sigFolders = new String[] { "misc/ordering.als" };
//	static String[] sigFolders = new String[] { "misc/enum/enum1.als" };
//	static String[] sigFolders = new String[] { "..\\models-master\\simple-models\\state-machine\\flip-flop.als"};

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
		A4Solution ans = ModuleDiff.diff(f.toString(), "misc/empty.als");
		assertTrue(f.toString() + " had a satisfiable diff with empty module", !ans.satisfiable() || size(ans) == 0);
	}

	@SuppressWarnings("resource")
	public static Stream<Arguments> allAlloyFiles() throws Exception {
		Stream<Arguments> allFiles = null;
		for (String folder : sigFolders) {
			Stream<Arguments> inThisFolder = Files
					.find(Paths.get(folder), Integer.MAX_VALUE,
							(filePath, fileAttr) -> fileAttr.isRegularFile() && filePath.toString().endsWith(".als"))
					.map(f -> Arguments.of(f));
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
		A4Solution ans = ModuleDiff.diff("misc/empty.als", f.toString());

		if (ans.satisfiable()) {
			assertTrue("Empty module had an empty diff with " + f.toString(), size(ans) > 0);
		} else {
			A4Solution ansF = ModuleDiff.getSolution(f.toString());
			if (ansF.satisfiable()
					&& !CompUtil.parseEverything_fromFile(null, null, f.toString()).getAllCommands().get(0).check) {
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

	/**
	 * Checks whether the current module has instances that it doesn't.
	 * This should always be false.
	 * 
	 * @param f
	 */
	@ParameterizedTest
	@MethodSource("allAlloyFiles")
	public void diffSelfSelf(Path f) {
		System.out.println("diff " + f.toString() + " and itself");
		A4Solution ans = ModuleDiff.diff(f.toString(), f.toString());
		assertFalse(f.toString() + " had a satisfiable diff with itself", ans.satisfiable());
	}

	public static Path previous = null;
	
	@ParameterizedTest
	@MethodSource("allAlloyFiles")
	public void diffPreviousSelf(Path f) {
		if (previous != null) {
			System.out.println("diff " + previous.toString() + " and " + f.toString());
			try {
				ModuleDiff.diff(previous.toString(), f.toString(),10, true);
			} catch (Exception e) {
				previous = f;
				throw e;
			}
		}
		previous = f;
	}
	
	@Test
	public void diffExtends12() {
		A4Solution ans = ModuleDiff.diff("misc/inheritance/extends1v1.als", "misc/inheritance/extends1v2.als");
		assertFalse(ans.satisfiable());

		// this is true because of the scope of inheritance
		ans = ModuleDiff.diff("misc/inheritance/extends1v2.als", "misc/inheritance/extends1v1.als");
		assertTrue(ans.satisfiable());
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
	}

	@Test
	public void diffPaper() {
		// v2 refines v1

		// no instance of v2 that is not in v1
		A4Solution ans = ModuleDiff.diff("misc/paper/v1.als", "misc/paper/v2.als");
		assertFalse(ans.satisfiable());
		// some instance of v1 that is not in v2
		ans = ModuleDiff.diff("misc/paper/v2.als", "misc/paper/v1.als");
		assertTrue(ans.satisfiable());

		// v3 refines v1

		// no instance of v3 that is not in v1
		ans = ModuleDiff.diff("misc/paper/v1.als", "misc/paper/v3.als");
		assertFalse(ans.satisfiable());
		// some instance of v1 that is not in v3
		ans = ModuleDiff.diff("misc/paper/v3.als", "misc/paper/v1.als");
		assertTrue(ans.satisfiable());

		// v2 eq v3
		ans = ModuleDiff.diff("misc/paper/v2.als", "misc/paper/v3.als");
		assertFalse(ans.satisfiable());

		ans = ModuleDiff.diff("misc/paper/v3.als", "misc/paper/v3.als");
		assertFalse(ans.satisfiable());
	}

	@Test
//	@Ignore
	public void diffFarmer() {
		String farmerFile = "../iAlloy-dataset-master/mutant_version_set/farmer/v1/farmer.als";
//		A4Solution ans = ModuleDiff.diff("misc/empty.als", farmerFile);
		A4Solution ans = ModuleDiff.diff(farmerFile, farmerFile);
		assertTrue(ans.satisfiable());
	}
	
	@Test
//	@Ignore
	public void diffTransitiveClosure() {
		String file = "misc/transitiveClosure.als";
		A4Solution ans = ModuleDiff.diff("misc/empty.als", file, 10, false);
//		ans = ModuleDiff.diff(file, "misc/empty.als");
		assertTrue(ans.satisfiable());
	}

}
