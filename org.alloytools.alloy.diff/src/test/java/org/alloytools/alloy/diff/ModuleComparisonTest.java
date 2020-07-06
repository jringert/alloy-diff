package org.alloytools.alloy.diff;

import static org.junit.jupiter.api.Assertions.assertTrue;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Stream;

import org.alloytools.alloy.instcheck.CheckSolution;
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
//	static String[] sigFolders = new String[] { "..\\models-master\\simple-models\\state-machine\\flip-flop.als"};

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
				Command v2cmd = new Command(false, -1, -1, -1, v2.getAllReachableFacts());

				A4Options options = new A4Options();
				options.solver = A4Options.SatSolver.SAT4J;

				A4Solution sol = ModuleDiff.diff(previous.toString(), f.toString(), true);
				
				List<A4Solution> sols = new ArrayList<>();

				// have to calculate in advance otherwise solver has NullPointers when trying to
				// get next solution
				while (sol.satisfiable() && sols.size() < 1) {
					sols.add(sol);
					sol = sol.next();
				}
				for (A4Solution s : sols) {
					System.out.println(s);
					assertTrue(CheckSolution.check(v2.getAllReachableUserDefinedSigs(), v2cmd, s, options));
				}
			} catch (Exception e) {
				previous = f;
				throw e;
			}
		}
		previous = f;
	}
	

}
