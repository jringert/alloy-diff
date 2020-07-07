package org.alloytools.alloy.diff;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.ScopeComputer;

public class CommandGenerator {

	private ModuleMerger m;

	public CommandGenerator(ModuleMerger merger) {
		this.m = merger;
	}

	/**
	 * compute a run command for diff(v1, v2) = sem(v2) \ sem(v1)
	 * 
	 * @param v1
	 * @param v2
	 * @param scope    the maximum scope for comparison (might be overriden by Alloy
	 *                 due to inheitance), if withPred==true the scope will be
	 *                 overriden by min(manual scope, default scope)
	 * @param withPred take the predicate of the first command into account
	 *                 (otherwise only signatures and facts but ignores original
	 *                 command)
	 * @return
	 */
	public Command generateDiffCommand(Module v1, Module v2, int scope, boolean withPred) {

		Command cmd1 = v1.getAllCommands().get(0);
		Command cmd2 = v2.getAllCommands().get(0);

		int bitwidth = 0;
		int maxInt = m.maxInt;

		Expr c1 = null;
		Expr c2 = null;

		if (withPred) {
			c1 = m.c1.and(m.replaceSigRefs(cmd1.formula, true));
			c2 = m.c2.and(m.replaceSigRefs(cmd2.formula, false));
		} else {
			c1 = m.c1.and(m.replaceSigRefs(v1.getAllReachableFacts(), true));
			c2 = m.c2.and(m.replaceSigRefs(v2.getAllReachableFacts(), false));
		}

		if (scope == -1) {
			scope = 3;
		}

		Command cmd4scope = new Command(false, scope, -1, -1, ExprConstant.TRUE);
		ScopeComputer sc1 = ScopeComputer.compute(new A4Reporter(), new A4Options(), m.v1Sigs.values(), cmd4scope).b;
		ScopeComputer sc1orig = ScopeComputer.compute(new A4Reporter(), new A4Options(), m.v1Sigs.values(), cmd1).b;
		ScopeComputer sc2 = ScopeComputer.compute(new A4Reporter(), new A4Options(), m.v2Sigs.values(), cmd4scope).b;
		ScopeComputer sc2orig = ScopeComputer.compute(new A4Reporter(), new A4Options(), m.v2Sigs.values(), cmd2).b;
		if (!withPred) {
			sc1orig = sc1;
			sc2orig = sc2;
		}

		// restrict union of children to scope of parent in v1
		for (Sig parent : m.v1iu.getParentSigs()) {
			Expr union = null;
			int ones = 0;
			for (Sig child : m.v1iu.getSubSigs(parent)) {
				Sig s = m.sigs.get(child.label);
				if (s != null) {
					// ones override the default scope (important for enums!)
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
				Sig p = m.sigs.get(parent.label);
				if (p != null) {
					union = union.plus(p);
				}

				int scopeInOrig = Math.min(sc1.sig2scope(parent), sc1orig.sig2scope(parent));
				if (sc1.isExact(parent) || cmd1.additionalExactScopes.contains(parent)) {
					c1 = c1.and(union.cardinality().equal(ExprConstant.makeNUMBER(Math.max(ones, scopeInOrig))));
				} else {
					c1 = c1.and(union.cardinality().lte(ExprConstant.makeNUMBER(Math.max(ones, scopeInOrig))));
				}
				maxInt = Math.max(maxInt, Math.max(ones, scopeInOrig));
			}
		}
		// restrict union of children to scope of parent in v2
		for (Sig parent : m.v2iu.getParentSigs()) {
			Expr union = null;
			int ones = 0;
			for (Sig child : m.v2iu.getSubSigs(parent)) {
				Sig s = m.sigs.get(child.label);
				if (s != null) {
					// ones override the default scope (important for enums!)
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
				Sig p = m.sigs.get(parent.label);
				if (p != null) {
					union = union.plus(p);
				}

				int scopeInOrig = Math.min(sc2.sig2scope(parent), sc2orig.sig2scope(parent));
				if (sc2.isExact(parent) || cmd2.additionalExactScopes.contains(parent)) {
					c2 = c2.and(union.cardinality().equal(ExprConstant.makeNUMBER(Math.max(ones, scopeInOrig))));
				} else {
					c2 = c2.and(union.cardinality().lte(ExprConstant.makeNUMBER(Math.max(ones, scopeInOrig))));
				}
			}

		}

		for (Sig s : m.v1Sigs.values()) {
			maxInt = Math.max(maxInt, sc1.sig2scope(s));
		}
		for (Sig s : m.v2Sigs.values()) {
			maxInt = Math.max(maxInt, sc2.sig2scope(s));
		}
		while (maxInt > Util.max(bitwidth)) {
			bitwidth++;
		}

		Command cmd = new Command(false, scope, bitwidth, -1, c2.and(c1.not()));

		boolean changed = false;
		// update scope based on both modules
		for (String sName : m.sigs.keySet()) {
			Sig s = m.sigs.get(sName);

			Sig s1 = m.v1Sigs.get(sName);
			int scope1 = -1;
			boolean exact1 = cmd1.additionalExactScopes.contains(s1);
			if (s1 != null) {
				scope1 = Math.min(sc1.sig2scope(s1), sc1orig.sig2scope(s1));
				exact1 |= sc1.isExact(s1);
			}

			Sig s2 = m.v2Sigs.get(sName);
			int scope2 = -1;
			boolean exact2 = cmd2.additionalExactScopes.contains(s2);
			if (s2 != null) {
				scope2 = Math.min(sc2.sig2scope(s2), sc2orig.sig2scope(s2));
				exact2 |= sc2.isExact(s2);
			}

			if (Math.max(scope1, scope2) >= 1) {
				// note that 0 can be computed if scope is too small for all subsignatures
				// however, if we restrict it, Alloy complains with an error
				cmd = cmd.change(s, exact1 && exact2, Math.max(scope1, scope2));
			}
			// take care of one side exact
			if (s1 != null && exact1 && !exact2 && scope1 != -1) {
				c1 = c1.and(s.cardinality().equal(ExprConstant.makeNUMBER(scope1)));
				changed = true;
			}
			if (s2 != null && !exact1 && exact2 && scope2 != -1) {
				c2 = c2.and(s.cardinality().equal(ExprConstant.makeNUMBER(scope2)));
				changed = true;
			}
		}

		if (changed) {
			cmd = cmd.change(c2.and(c1.not()));
		}

		return cmd;
	}

}
