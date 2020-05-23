package org.alloytools.alloy.diff;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.parser.CompUtil;

public class StatsComputer {
	static String[] sigFolders = new String[] { "misc", "../models-master", "../iAlloy-dataset-master",
			"../platinum-experiment-data/" };

	public static void main(String[] args) throws IOException {
		for (String folder : sigFolders) {
			Files
					.find(Paths.get(folder), Integer.MAX_VALUE,
							(filePath, fileAttr) -> fileAttr.isRegularFile() && filePath.toString().endsWith(".als"))
					.forEach(f -> {
						try {
							writeStats(f);
						} catch (Exception e) {

						}
					});
		}
	}

	private static Object writeStats(Path f) throws IOException {
		CompModule m = CompUtil.parseEverything_fromFile(null, null, f.toString());
		String report = f.toString() + "; " + 
				Files.readAllLines(f).size() + "; " + 
				m.getAllReachableUserDefinedSigs().size() + "; " + 
				countFields(m.getAllReachableUserDefinedSigs()) + "; " +
				countFactFunPref(m) + "\r\n";
	
		Files.writeString(Paths.get("stats.csv"), report, StandardOpenOption.CREATE, StandardOpenOption.APPEND);
		return null;
	}

	private static int countFactFunPref(CompModule m) {
		int count = 0;
		for (CompModule rm : m.getAllReachableModules()) {
			if (!"util/integer".equals(rm.getModelName())) {
				count += rm.getAllFunc().size();
				count += rm.getAllFacts().size();
			}
		}
		for (Sig s : m.getAllReachableUserDefinedSigs()) {
			count += s.getFacts().size();
		}
		
		return count;
	}

	private static int countFields(ConstList<Sig> sigs) {
		int count = 0; 

		for (Sig s: sigs) {
			count += s.getFields().size();
		}
		return count;
	}
}
