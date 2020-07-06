package org.alloytools.alloy.diff;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;

import edu.mit.csail.sdg.translator.A4Solution;

public class DiffStatsComputer {

	public static void main(String[] args) throws IOException {
		boolean withPred = args.length == 4;
		writeStats(args[0], args[1], Integer.parseInt(args[2]), withPred);
	}

	private static void writeStats(String f1, String f2, int scope, boolean withPred) throws IOException {		
		long v12time = System.currentTimeMillis();
		A4Solution ans12 = ModuleDiff.diff(f1, f2, scope, withPred);
		int v12TotalVars = ModuleDiff.totalVarsSAT;
		v12time = System.currentTimeMillis() - v12time;

		String report = f1 + "; " + f2 + "; "
				+ v12TotalVars + "; " + v12time + "; " + ans12.satisfiable() 
				+ "\r\n";

		Files.writeString(Paths.get("statsDiff_" + scope + ".csv"), report, StandardOpenOption.CREATE,
				StandardOpenOption.APPEND);
	}
}
