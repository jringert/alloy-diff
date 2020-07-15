package edu.mit.csail.sdg.translator;

import java.util.Collection;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Sig;

/**
 * Simplified version of Alloy's ScopeComputer. This wrapper is required because
 * the original ScopeComputer is final and only has package visibility.
 *
 */
public class MyScopeComputer {
	private ScopeComputer sc;

	public MyScopeComputer(ScopeComputer sc) {
		this.sc = sc;
	}

	public static MyScopeComputer compute(A4Reporter a4Reporter, A4Options a4Options, Collection<Sig> values,
			Command cmd4scope) {
		return new MyScopeComputer(ScopeComputer.compute(a4Reporter, a4Options, values, cmd4scope).b);
	}

	public int sig2scope(Sig sig) {
		return sc.sig2scope(sig);
	}

	public boolean isExact(Sig sig) {
		return sc.isExact(sig);
	}

}
