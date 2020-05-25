package org.alloytools.alloy.diff;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;

import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

public class SolvingStatsComputerWithPred {
	static String[] sigFolders = new String[] { 
			"../models-master/algorithms/distributed-hashtable",
			"../models-master/software-abstractions-book/appendixA",
			"../models-master/software-abstractions-book/chapter2",
			"../models-master/software-abstractions-book/chapter4",
			"../iAlloy-dataset-master/mutant_version_set/addr",
			"../iAlloy-dataset-master/mutant_version_set/addressBook",
			"../iAlloy-dataset-master/mutant_version_set/arr",
			"../iAlloy-dataset-master/mutant_version_set/balancedBST",
			"../iAlloy-dataset-master/mutant_version_set/bempl",
			"../iAlloy-dataset-master/mutant_version_set/binaryTree",
			"../iAlloy-dataset-master/mutant_version_set/cd/",
			"../iAlloy-dataset-master/mutant_version_set/ceilingsAndFloors",
			"../iAlloy-dataset-master/mutant_version_set/dll",
			"../iAlloy-dataset-master/mutant_version_set/filesystem",
			"../iAlloy-dataset-master/mutant_version_set/fullTree",
			"../iAlloy-dataset-master/mutant_version_set/grade",
			"../iAlloy-dataset-master/mutant_version_set/grandpa1",
			"../iAlloy-dataset-master/mutant_version_set/grandpa2",
			"../iAlloy-dataset-master/mutant_version_set/grandpa3",
			"../iAlloy-dataset-master/mutant_version_set/handshake",
			"../iAlloy-dataset-master/mutant_version_set/lists",
			"../iAlloy-dataset-master/mutant_version_set/sll",
			"../iAlloy-dataset-master/mutant_version_set/student",
			"../iAlloy-dataset-master/real_version_set/addrFaulty",
			"../iAlloy-dataset-master/real_version_set/arr1",
			"../iAlloy-dataset-master/real_version_set/balancedBST1",
			"../iAlloy-dataset-master/real_version_set/balancedBST2",
			"../iAlloy-dataset-master/real_version_set/balancedBST3",
			"../iAlloy-dataset-master/real_version_set/bemplFaulty",
			"../iAlloy-dataset-master/real_version_set/cd1",
			"../iAlloy-dataset-master/real_version_set/cd2",
			"../iAlloy-dataset-master/real_version_set/dll1",
			"../iAlloy-dataset-master/real_version_set/dll2",
			"../iAlloy-dataset-master/real_version_set/dll3",
			"../iAlloy-dataset-master/real_version_set/dll4",
			"../iAlloy-dataset-master/real_version_set/gradeFaulty",
			"../iAlloy-dataset-master/real_version_set/student0",
			"../iAlloy-dataset-master/real_version_set/student1",
			"../iAlloy-dataset-master/real_version_set/student10",
			"../iAlloy-dataset-master/real_version_set/student11",
			"../iAlloy-dataset-master/real_version_set/student12",
			"../iAlloy-dataset-master/real_version_set/student13",
			"../iAlloy-dataset-master/real_version_set/student14",
			"../iAlloy-dataset-master/real_version_set/student15",
			"../iAlloy-dataset-master/real_version_set/student16",
			"../iAlloy-dataset-master/real_version_set/student17",
			"../iAlloy-dataset-master/real_version_set/student18",
			"../iAlloy-dataset-master/real_version_set/student19",
			"../iAlloy-dataset-master/real_version_set/student2",
			"../iAlloy-dataset-master/real_version_set/student3",
			"../iAlloy-dataset-master/real_version_set/student4",
			"../iAlloy-dataset-master/real_version_set/student5",
			"../iAlloy-dataset-master/real_version_set/student6",
			"../iAlloy-dataset-master/real_version_set/student7",
			"../iAlloy-dataset-master/real_version_set/student8",
			"../iAlloy-dataset-master/real_version_set/student9",
			"../platinum-experiment-data/comparison/CSOS",
			"../platinum-experiment-data/comparison/Decider",
			"../platinum-experiment-data/comparison/Ecommerce",
			"../platinum-experiment-data/evolved/CSOSMutants_Evolve",
			"../platinum-experiment-data/evolved/DeciderMutants_Evolve",
			"../platinum-experiment-data/evolved/EcommerceMutants_Evolve",
			"../platinum-experiment-data/evolved/WordpressMutants_Evolve",
			"../platinum-experiment-data/paired/CSOSMutants",
			"../platinum-experiment-data/paired/DeciderMutants",
			"../platinum-experiment-data/paired/EcommerceMutants",
			"../platinum-experiment-data/paired/WordpressMutants",
			"../platinum-experiment-data/scope/CSOSScope",
			"../platinum-experiment-data/scope/DeciderScope",
			"../platinum-experiment-data/scope/EcommerceScope",
			"../platinum-experiment-data/scope/WordpressScope",
 };
	
	
	private static int scope = 3;
	private static A4Options options = new A4Options();

	public static void main(String[] args) throws IOException {
		if (System.getProperty("os.name").contains("indows")) {
			options.solver = A4Options.SatSolver.SAT4J;
		} else {
			options.solver = A4Options.SatSolver.CryptoMiniSatJNI;
		}
		while (scope <= 60) {
			for (String folder : sigFolders) {
				previous = null;
				Files
				.find(Paths.get(folder), Integer.MAX_VALUE,
						(filePath, fileAttr) -> fileAttr.isRegularFile() && filePath.toString().endsWith(".als"))
				.forEach(f -> {
					try {
						writeStats(f);
					} catch (Exception e) {
						System.out.println(e.getMessage());
					}
				});
			}
			scope += 5;
		}
	}
	
	private static Path previous = null;

	private static void writeStats(Path f) throws IOException {		
		if (previous != null) {
			try {
				
				long v1time = System.currentTimeMillis();
				CompModule v1 = CompUtil.parseEverything_fromFile(null, null, previous.toString());
				Command cmd1 = v1.getAllCommands().get(0);
				Command v1cmd = new Command(false, scope, -1, -1, cmd1.formula);
				A4Solution ans1 = TranslateAlloyToKodkod.execute_command(ModuleDiff.rep, v1.getAllReachableUserDefinedSigs(), v1cmd, options);
				int v1TotalVars = ModuleDiff.totalVarsSAT;
				v1time = System.currentTimeMillis() - v1time;
				
				long v2time = System.currentTimeMillis();
				CompModule v2 = CompUtil.parseEverything_fromFile(null, null, f.toString());
				Command cmd2 = v2.getAllCommands().get(0);
				Command v2cmd = new Command(false, scope, -1, -1, cmd2.formula);
				A4Solution ans2 = TranslateAlloyToKodkod.execute_command(ModuleDiff.rep, v2.getAllReachableUserDefinedSigs(), v2cmd, options);
				int v2TotalVars = ModuleDiff.totalVarsSAT;
				v2time = System.currentTimeMillis() - v2time;
				if (v2TotalVars + v1TotalVars != 0) {
					long v12time = System.currentTimeMillis();
					A4Solution ans12 = ModuleDiff.diff(previous.toString(), f.toString(), scope);
					int v12TotalVars = ModuleDiff.totalVarsSAT;
					v12time = System.currentTimeMillis() - v12time;
					
					long v21time = System.currentTimeMillis();
					A4Solution ans21 = ModuleDiff.diff(f.toString(), previous.toString(), scope);
					int v21TotalVars = ModuleDiff.totalVarsSAT;
					v21time = System.currentTimeMillis() - v21time;
					
					String report = previous.toString() + "; " +
							f.toString() + "; " +
							v1TotalVars + "; " +
							v1time + "; " +
							ans1.satisfiable() + ";" +
							v2TotalVars + "; " +
							v2time + "; " +
							ans2.satisfiable() + ";" +
							v12TotalVars + "; " +
							v12time + "; " +							
							ans12.satisfiable() + ";" + 
							v21TotalVars + "; " +
							v21time + "; " +
							ans21.satisfiable() + ";" + 
							classify(ans12.satisfiable(), ans21.satisfiable(), ans1.satisfiable(), ans2.satisfiable()) + "\r\n";
					
					Files.writeString(Paths.get("cnfDiffWithPred_" + scope + ".csv"), report, StandardOpenOption.CREATE, StandardOpenOption.APPEND);
				}
				
			} catch (Exception e) {
				System.out.println(e.getMessage());
			}
		}
		previous = f;
	}

	private static String classify(boolean satisfiable12, boolean satisfiable21, boolean s1, boolean s2) {
		if (satisfiable12 && satisfiable21) {
			return "incomparable";
		}
		if (satisfiable12 && !satisfiable21) {
			if (!s1) {
				return "extension-empty1";	
			}
			return "extension";
		}
		if (!satisfiable12 && satisfiable21) {
			if (!s2) {
				return "refinement-empty2";	
			}
			return "refinement";
		}
		if (!satisfiable12 && !satisfiable21) {
			if (!s1 && !s2) {
				return "refactoring-empty";	
			}
			return "refactoring";
		}
		return "";
	}

}
