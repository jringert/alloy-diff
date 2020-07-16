package org.alloytools.alloy.diff;

import static org.junit.jupiter.api.Assertions.assertTrue;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Stream;

import org.alloytools.alloy.instcheck.CheckSolution;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;

public class ModuleComparisonTest {

	static String[] sigFolders = new String[] { "misc", "../models-master", "../iAlloy-dataset-master",
			"../platinum-experiment-data/" };
	
	static int scope = 8; // default scope of Alloy

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


	public static Path previous = null;
	
	@ParameterizedTest
	@MethodSource("allAlloyFiles")
	public void diffPreviousSelf(Path f) {
		if (previous != null) {
			System.out.println("diff " + previous.toString() + " and " + f.toString());
			try {
				Module v2 = null;
				try {
					v2 = CompUtil.parseEverything_fromFile(null, null, f.toString());
				} catch (Exception e) {
					// ignore parsing errors
					return;
				}

				A4Options options = new A4Options();
				options.solver = A4Options.SatSolver.CryptoMiniSatJNI;
				A4Solution sol = null;

				try {
					sol = ModuleDiff.diff(previous.toString(), f.toString(), scope, false);
				} catch (Exception e) {
					if (e.getMessage() == null || 
							(!e.getMessage().contains("Ordering") &&
							!e.getMessage().contains("higher-order") &&
							!e.getMessage().contains("integer.als") && 
							!e.getMessage().contains("File cannot be found"))) {
						throw e;
					} else {
						// exception was expected... stop here
						return;
					}
				}

				Command v2cmd = new Command(false, scope, sol.getBitwidth(), sol.getMaxSeq(), v2.getAllReachableFacts());
				
				List<A4Solution> sols = new ArrayList<>();

				// have to calculate in advance otherwise solver has NullPointers when trying to
				// get next solution
				while (sol.satisfiable() && sols.size() < 1) {
					sols.add(sol);
					sol = sol.next();
				}
				for (A4Solution s : sols) {
					System.out.println(s);
					assertTrue(CheckSolution.check(v2.getAllReachableUserDefinedSigs(), v2cmd, s, options), previous.toString() + " " + f.toString() + " have a witness that is not in the latter");
				}
			} catch (Exception e) {
				previous = f;
				throw e;
			}
		}
		previous = f;
	}
	
	
	@Test
	void specialCase() {
		previous = Paths.get("../iAlloy-dataset-master/mutant_version_set/arr/v4/arr.als");
		Path current = Paths.get("../iAlloy-dataset-master/mutant_version_set/arr/v5/arr.als");
		diffPreviousSelf(current);		
	}

}
