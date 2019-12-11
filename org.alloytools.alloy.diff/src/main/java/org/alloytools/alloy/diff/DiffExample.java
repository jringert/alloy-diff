package org.alloytools.alloy.diff;

import edu.mit.csail.sdg.alloy4.Err;

/**
 * This class demonstrates how to access Alloy4 via the compiler methods.
 */

public final class DiffExample {

	public static void main(String[] args) throws Err {

		ModuleMerger m = new ModuleMerger("misc/File1.als", "misc/File2.als");		
	}

}
