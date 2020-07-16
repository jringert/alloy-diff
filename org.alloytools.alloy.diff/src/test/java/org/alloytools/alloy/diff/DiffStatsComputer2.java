package org.alloytools.alloy.diff;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.util.Set;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;
import edu.mit.csail.sdg.translator.A4Options.SatSolver;

public class DiffStatsComputer2 {

	public static void main(String[] args) throws IOException {
		boolean withPred = args.length == 4;
		try {
			writeStats(args[0], args[1], Integer.parseInt(args[2]), withPred);
		} catch (Exception e) {
			// TODO: handle exception
		}
	}

	private static void writeStats(String f1, String f2, int scope, boolean withPred) throws IOException {
		A4Options options = new A4Options();
		options.solver = SatSolver.CryptoMiniSatJNI;
		
		long v1time = System.currentTimeMillis();
		CompModule v1 = CompUtil.parseEverything_fromFile(null, null, f1);
		Command cmd1 = v1.getAllCommands().get(0);
		Command v1cmd = new Command(false, scope, cmd1.bitwidth, -1, cmd1.formula);
		ConstList<Sig> sigs = v1.getAllReachableUserDefinedSigs();
		for (Sig sig : sigs) {
			if (cmd1.getScope(sig) != null) {
				int min = scope;
				if (v1cmd.getScope(sig) != null) {
					min = v1cmd.getScope(sig).endingScope;
				}
				v1cmd = v1cmd.change(sig, cmd1.getScope(sig).isExact, Math.min(min, cmd1.getScope(sig).endingScope));
			}
		}
		A4Solution ans1 = TranslateAlloyToKodkod.execute_command(ModuleDiff.rep, sigs, v1cmd, options);
		int v1TotalVars = ModuleDiff.totalVarsSAT;
		v1time = System.currentTimeMillis() - v1time;

		String report = f1 + "; " 
				+ v1TotalVars + "; " + v1time + "; " + ans1.satisfiable() 
				+ "\r\n";

		Files.writeString(Paths.get("statsV1_" + scope + ".csv"), report, StandardOpenOption.CREATE,
				StandardOpenOption.APPEND);
	}
}
