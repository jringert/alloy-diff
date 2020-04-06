package org.alloytools.alloy.flatten;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.ast.Sig.PrimSig;
import edu.mit.csail.sdg.ast.Sig.SubsetSig;

/**
 * Flatten all modules to remove inheritance.
 * 
 * @author ringert
 *
 */
public class ModuleFlattener {

	/**
	 * map from original signatures to fields
	 */
	private Map<Sig, Set<Field>> oldFields = new LinkedHashMap<Sig, Set<Field>>();

	public ModuleFlattener(Module m) {
		for (Sig s : m.getAllReachableSigs()) {
			if (s instanceof PrimSig) {
				oldFields.put(s, computeTransitiveExtendsFields(s));
			}
		}
		for (Sig s : m.getAllReachableSigs()) {
			if (s instanceof SubsetSig) {
				addFieldsSubsetSig(s, new LinkedHashSet<>());
			}
		}

		Module mFlat = new FlatModule();

	}

	/**
	 * adds fields upwards through subset signatures to the first primitive
	 * signature
	 * 
	 * @param s
	 * @param fields
	 */
	private void addFieldsSubsetSig(Sig s, Set<Field> fields) {
		if (s instanceof SubsetSig) {
			for (Field f : s.getFields()) {
				fields.add(f);
			}
			for (Sig p : ((SubsetSig) s).parents) {
				addFieldsSubsetSig(p, new LinkedHashSet<Field>(fields));
			}
		} else {
			oldFields.get(s).addAll(fields);
		}
	}

	/**
	 * extends flattens from all transitive parent classes
	 * 
	 * @param s
	 * @return
	 */
	private Set<Field> computeTransitiveExtendsFields(Sig s) {
		Set<Field> fields = new LinkedHashSet<>();
		for (Field f : s.getFields()) {
			fields.add(f);
		}
		if (s instanceof PrimSig) {
			Sig parent = ((PrimSig) s).parent;
			if (parent != null) {
				fields.addAll(computeTransitiveExtendsFields(parent));
			}
		}
		return fields;
	}

	public static Module flatten(Module m) {
		ModuleFlattener flattener = new ModuleFlattener(m);

		return m;
	}
}
