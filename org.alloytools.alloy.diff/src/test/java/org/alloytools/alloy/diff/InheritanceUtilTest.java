package org.alloytools.alloy.diff;

import static org.junit.Assert.*;

import org.junit.Test;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.parser.CompUtil;

public class InheritanceUtilTest {
	private A4Reporter rep = new A4Reporter() {
		@Override
		public void warning(ErrorWarning msg) {
			System.out.print("Relevance Warning:\n" + (msg.toString().trim()) + "\n\n");
			System.out.flush();
		}
	};

	@Test
	public void testSubs() {
		Module m = CompUtil.parseEverything_fromFile(rep, null, "misc/inheritance/extends1.als");
		InheritanceUtil iu = new InheritanceUtil(m);

		assertEquals(3, iu.getSubSigs(getSig(m, "A")).size());
		assertEquals(1, iu.getSubSigs(getSig(m, "B")).size());
		assertNull(iu.getSubSigs(getSig(m, "C")));
		assertNull(iu.getSubSigs(getSig(m, "D")));
	}
	
	@Test
	public void testNullSubs() {
		Module m = CompUtil.parseEverything_fromFile(rep, null, "misc/inheritance/extends1_flattened_direct.als");
		InheritanceUtil iu = new InheritanceUtil(m);

		assertNull(iu.getSubSigs(getSig(m, "A")));
		assertNull(iu.getSubSigs(getSig(m, "B")));
		assertNull(iu.getSubSigs(getSig(m, "C")));
		assertNull(iu.getSubSigs(getSig(m, "D")));
	}	

	private Sig getSig(Module m, String sigName) {
		for (Sig s : m.getAllSigs()) {
			if (s.label.endsWith(sigName)) {
				return s;
			}
		}
		return null;
	}

}
