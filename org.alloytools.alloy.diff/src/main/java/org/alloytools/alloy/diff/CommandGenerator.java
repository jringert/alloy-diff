package org.alloytools.alloy.diff;

import java.util.ArrayList;
import java.util.List;

import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.CommandScope;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;

public class CommandGenerator {
	
	private ModuleMerger m;
	
	public CommandGenerator(ModuleMerger merger) {
		this.m = merger;
	}

	/**
	 * a run command diffing the two original commands
	 * 
	 * @param v1
	 * @param v2
	 * @return
	 */
	public Command generateDiffCommand(Module v1, Module v2) {

		Command cmd1 = v1.getAllCommands().get(0);
		Command cmd2 = v2.getAllCommands().get(0);

		int overall = Math.max(cmd1.overall, cmd2.overall);
		overall = Math.max(overall, 4); // FIXME not needed if inheritance scope is taken into account
		int bitwidth = Math.max(cmd1.bitwidth, cmd2.bitwidth);
		int maxseq = Math.max(cmd1.maxseq, cmd2.maxseq);

		m.c1 = m.c1.and(m.replaceSigRefs(cmd1.formula, true));
		m.c2 = m.c2.and(m.replaceSigRefs(cmd2.formula, false));

		Command cmd = new Command(false, overall, bitwidth, maxseq, m.c2.and(m.c1.not()));

		for (Sig s : m.sigs.values()) {
			CommandScope s1 = cmd1.getScope(m.v1Sigs.get(s.label));
			CommandScope s2 = cmd2.getScope(m.v2Sigs.get(s.label));

			int scope = -1;
			boolean exact = false;

			// take scope from v1
			if (s1 != null) {
				scope = Math.max(scope, s1.endingScope);
				exact |= s1.isExact;
			}
			// or take scope from v1
			if (s2 != null) {
				scope = Math.max(scope, s2.endingScope);
				exact |= s2.isExact;
			}

			// FIXME take inheritance scopes into account

			if (scope != -1) {
				cmd = cmd.change(s, exact, scope);
			}

			if (cmd1.additionalExactScopes.contains(m.v1Sigs.get(s.label))
					|| cmd2.additionalExactScopes.contains(m.v2Sigs.get(s.label))) {
				List<Sig> exactScopes = new ArrayList<>(cmd.additionalExactScopes);
				exactScopes.add(s);
				cmd = cmd.change(exactScopes.toArray(new Sig[] {}));
			}
		}

//		return new Command(false, -1, -1, -1, c2.and(c1.not()));
		return cmd;
	}

	/**
	 * a run command diffing the two original commands
	 * 
	 * @param v1
	 * @param v2
	 * @return
	 */
	public Command generatePlainDiffCommand(Module v1, Module v2, int scope) {

		Command cmd1 = v1.getAllCommands().get(0);
		Command cmd2 = v2.getAllCommands().get(0);

		m.c1 = m.c1.and(m.replaceSigRefs(v1.getAllReachableFacts(), true));
		m.c2 = m.c2.and(m.replaceSigRefs(v2.getAllReachableFacts(), false));
		
		// c1 = removeC1conjunctsFromC2(c2, c1);
		
		if (scope == -1) {
			scope = 3;
		}
		for (Sig parent : m.v1iu.getParentSigs()) {			
			Expr union = null;
			int ones = 0;
			for (Sig child : m.v1iu.getSubSigs(parent)) {
				Sig s = m.sigs.get(child.label);
				if (s != null) {
					if (s.isOne != null) {
						ones++;
					}
					if (union == null) {
						union = s;
					} else {
						union = union.plus(s);
					}					
				}
			}
			if (union != null) {
				m.c1 = m.c1.and(union.cardinality().lte(ExprConstant.makeNUMBER(Math.max(ones, scope))));
			}
		}		
		for (Sig parent : m.v2iu.getParentSigs()) {
			Expr union = null;
			for (Sig child : m.v2iu.getSubSigs(parent)) {
				Sig s = m.sigs.get(child.label);
				if (s != null) {
					if (union == null) {
						union = s;
					} else {
						union = union.plus(s);
					}					
				}
			}
			if (union != null) {
				m.c2 = m.c2.and(union.cardinality().lte(ExprConstant.makeNUMBER(scope)));
			}
		}
		
		
		Command cmd = new Command(false, scope, 7, -1, m.c2.and(m.c1.not()));

		// this looks wrong in case only one module introduces an exact scope
		for (Sig s : m.sigs.values()) {
			if (cmd1.additionalExactScopes.contains(m.v1Sigs.get(s.label))
					|| cmd2.additionalExactScopes.contains(m.v2Sigs.get(s.label))) {
				List<Sig> exactScopes = new ArrayList<>(cmd.additionalExactScopes);
				exactScopes.add(s);
				cmd = cmd.change(exactScopes.toArray(new Sig[] {}));
			}
		}

		return cmd;
	}
	

	/**
	 * a run command diffing the two original commands
	 * 
	 * @param v1
	 * @param v2
	 * @return
	 */
	public Command generatePlainConjunctionCommand(Module v1, Module v2, int scope) {

		Command cmd1 = v1.getAllCommands().get(0);
		Command cmd2 = v2.getAllCommands().get(0);

		m.c1 = m.c1.and(m.replaceSigRefs(v1.getAllReachableFacts(), true));
		m.c2 = m.c2.and(m.replaceSigRefs(v2.getAllReachableFacts(), false));

		Command cmd = new Command(false, scope, -1, -1, m.c1.and(m.c2));

		for (Sig s : m.sigs.values()) {
			if (cmd1.additionalExactScopes.contains(m.v1Sigs.get(s.label))
					|| cmd2.additionalExactScopes.contains(m.v2Sigs.get(s.label))) {
				List<Sig> exactScopes = new ArrayList<>(cmd.additionalExactScopes);
				exactScopes.add(s);
				cmd = cmd.change(exactScopes.toArray(new Sig[] {}));
			}
		}

		return cmd;
	}

	public Command generatePredDiffCommand(Module v1, Module v2, int scope) {
		Command cmd1 = v1.getAllCommands().get(0);
		Command cmd2 = v2.getAllCommands().get(0);

		m.c1 = m.c1.and(m.replaceSigRefs(cmd1.formula, true));
		m.c2 = m.c2.and(m.replaceSigRefs(cmd2.formula, false));
		
		if (scope == -1) {
			scope = 3;
		}
		for (Sig parent : m.v1iu.getParentSigs()) {			
			Expr union = null;
			int ones = 0;
			for (Sig child : m.v1iu.getSubSigs(parent)) {
				Sig s = m.sigs.get(child.label);
				if (s != null) {
					if (s.isOne != null) {
						ones++;
					}
					if (union == null) {
						union = s;
					} else {
						union = union.plus(s);
					}					
				}
			}
			if (union != null) {
				m.c1 = m.c1.and(union.cardinality().lte(ExprConstant.makeNUMBER(Math.max(ones, scope))));
			}
		}		
		for (Sig parent : m.v2iu.getParentSigs()) {
			Expr union = null;
			for (Sig child : m.v2iu.getSubSigs(parent)) {
				Sig s = m.sigs.get(child.label);
				if (s != null) {
					if (union == null) {
						union = s;
					} else {
						union = union.plus(s);
					}					
				}
			}
			if (union != null) {
				m.c2 = m.c2.and(union.cardinality().lte(ExprConstant.makeNUMBER(scope)));
			}
		}
		
		
		Command cmd = new Command(false, scope, 7, -1, m.c2.and(m.c1.not()));

		for (Sig s : m.sigs.values()) {
			if (cmd1.additionalExactScopes.contains(m.v1Sigs.get(s.label))
					|| cmd2.additionalExactScopes.contains(m.v2Sigs.get(s.label))) {
				List<Sig> exactScopes = new ArrayList<>(cmd.additionalExactScopes);
				exactScopes.add(s);
				cmd = cmd.change(exactScopes.toArray(new Sig[] {}));
			}
		}

		return cmd;
	}
}
