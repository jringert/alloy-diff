package org.alloytools.alloy.diff;

import edu.mit.csail.sdg.alloy4.A4Reporter;
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
	 * a run command diffing the two original commands
	 * 
	 * @param v1
	 * @param v2
	 * @return
	 */
	public Command generateDiffCommand(Module v1, Module v2, int scope, boolean withPred) {

		Command cmd1 = v1.getAllCommands().get(0);
		Command cmd2 = v2.getAllCommands().get(0);
		
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

		Command cmd4scope = new Command(false, scope, 7, -1, ExprConstant.TRUE);
		ScopeComputer sc1 = ScopeComputer.compute(new A4Reporter(), new A4Options(), m.v1Sigs.values(), cmd4scope).b;
		
		ScopeComputer sc2 = ScopeComputer.compute(new A4Reporter(), new A4Options(), m.v2Sigs.values(), cmd4scope).b;
		
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
				
				int scopeInOrig = sc1.sig2scope(parent);
				if (sc1.isExact(parent) || cmd1.additionalExactScopes.contains(parent)) {
					c1 = c1.and(union.cardinality().equal(ExprConstant.makeNUMBER(Math.max(ones, scopeInOrig))));
				} else {
					c1 = c1.and(union.cardinality().lte(ExprConstant.makeNUMBER(Math.max(ones, scopeInOrig))));
				}
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

				int scopeInOrig = sc2.sig2scope(parent);
				if (sc2.isExact(parent) || cmd2.additionalExactScopes.contains(parent)) {
					c2 = c2.and(union.cardinality().equal(ExprConstant.makeNUMBER(Math.max(ones, scopeInOrig))));
				} else {
					c2 = c2.and(union.cardinality().lte(ExprConstant.makeNUMBER(Math.max(ones, scopeInOrig))));
				}
			}

		}
		
		
		Command cmd = new Command(false, scope, 7, -1, c2.and(c1.not()));
		
		boolean changed = false;
		// this looks wrong in case only one module introduces an exact scope
		for (String sName : m.sigs.keySet()) {
			Sig s = m.sigs.get(sName);
			
			Sig s1 = m.v1Sigs.get(sName);
			int scope1 = 0;
			boolean exact1 = cmd1.additionalExactScopes.contains(s1);
			if (s1 != null) {
				scope1 = sc1.sig2scope(s1);
				exact1 |= sc1.isExact(s1); 
			}
			
			Sig s2 = m.v2Sigs.get(sName);
			int scope2 = 0;
			boolean exact2 = cmd2.additionalExactScopes.contains(s2);
			if (s2 != null) {
				scope2 = sc2.sig2scope(s2);
				exact2 |= sc2.isExact(s2); 
			}

			cmd = cmd.change(s, exact1 && exact2, Math.max(scope1, scope2));
			// take care of one side exact
			if (s1 != null && exact1 && !exact2) {
				c1 = c1.and(s.cardinality().equal(ExprConstant.makeNUMBER(scope1)));
				changed = true;
			}
			if (s2 != null && !exact1 && exact2) {
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
