package org.alloytools.alloy.diff;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import org.junit.BeforeClass;
import org.junit.Test;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.parser.CompUtil;

public class ModuleMergerTest {

	public static A4Reporter rep;

	@BeforeClass
	public static void setup() {
		rep = new A4Reporter() {
			@Override
			public void warning(ErrorWarning msg) {
				System.out.print("Relevance Warning:\n" + (msg.toString().trim()) + "\n\n");
				System.out.flush();
			}
		};
	}

	/**
	 * tests if two modules signature counts have changed when they are not supposed
	 * to change Ex. If both modules have signature names that do not match then,
	 * then the merged module should have all signatures
	 */
	@Test
	public void testSignatureCountV1() {

		Module v1 = CompUtil.parseEverything_fromFile(rep, null, "misc/multiplicities/tests/testSignatureCountv1.als");
		Module v2 = CompUtil.parseEverything_fromFile(rep, null, "misc/multiplicities/tests/testSignatureCountv2.als");

		int v1SigsCount = v1.getAllSigs().size();
		int v2SigsCount = v1.getAllSigs().size();

		Collection<Sig> sigs = new ModuleMerger().mergeSigs(v1, v2);

		assertEquals(v1SigsCount + v2SigsCount, sigs.size());
	}

	/**
	 * tests if two modules signature counts have changed as needed Ex. If module 1
	 * has 2 signatures and module 2 has 2 signatures, and 1 signature name is
	 * common between both, then the merged module should have 3 signatures
	 */
	@Test
	public void testSignatureCountV2() {

		Module v1 = CompUtil.parseEverything_fromFile(rep, null,
				"misc/multiplicities/tests/v2testSignatureCountv1.als");
		Module v2 = CompUtil.parseEverything_fromFile(rep, null,
				"misc/multiplicities/tests/v2testSignatureCountv2.als");

		Collection<Sig> sigs = new ModuleMerger().mergeSigs(v1, v2);

		assertEquals(3, sigs.size());
	}

	/**
	 * tests if field names Ex. TODO
	 */
	@Test
	public void testFields() {

		Module v1 = CompUtil.parseEverything_fromFile(rep, null, "misc/multiplicities/tests/fieldTest1v1.als");
		Module v2 = CompUtil.parseEverything_fromFile(rep, null, "misc/multiplicities/tests/fieldTest1v2.als");

		Collection<Sig> sigs = new ModuleMerger().mergeSigs(v1, v2);

		assertEquals(3, sigs.size());

	}

	@Test
	public void selfMergeSigCountTest() throws Exception {
		Files.find(Paths.get("misc"), Integer.MAX_VALUE, (filePath, fileAttr) -> fileAttr.isRegularFile())
				.forEach(f -> selfMergeSigCount(f));
	}

	public void selfMergeSigCount(Path f) {
		String fName = f.toString();
		Module v1 = CompUtil.parseEverything_fromFile(rep, null, fName);

		int sigNum = v1.getAllSigs().size();

		Collection<Sig> sigs = new ModuleMerger().mergeSigs(v1, v1);

		assertEquals(sigNum, sigs.size());
	}

	@Test
	public void selfMergeWithEmptySigCountTest() throws Exception {
		Files.find(Paths.get("misc"), Integer.MAX_VALUE, (filePath, fileAttr) -> fileAttr.isRegularFile())
				.forEach(f -> selfMergeWithEmptySigCount(f));
	}

	public void selfMergeWithEmptySigCount(Path f) {
		String fName = f.toString();
		Module v1 = CompUtil.parseEverything_fromFile(rep, null, fName);
		Module empty = CompUtil.parseEverything_fromFile(rep, null, "misc/empty.als");

		int sigNum = v1.getAllSigs().size();

		Collection<Sig> sigs = new ModuleMerger().mergeSigs(v1, empty);

		assertEquals(sigNum, sigs.size());

		sigs = new ModuleMerger().mergeSigs(empty, v1);

		assertEquals(sigNum, sigs.size());

	}

	@Test
	public void selfMergeWithOneSigCountTest() throws Exception {
		Files.find(Paths.get("misc"), Integer.MAX_VALUE, (filePath, fileAttr) -> fileAttr.isRegularFile())
				.forEach(f -> selfMergeWithOneSigCount(f));
	}

	public void selfMergeWithOneSigCount(Path f) {
		String fName = f.toString();
		Module v1 = CompUtil.parseEverything_fromFile(rep, null, fName);
		Module one = CompUtil.parseEverything_fromFile(rep, null, "misc/one.als");

		if (fName.contains("misc/one.als") || fName.contains("misc\\one.als")) {
			return;
		}

		int sigNum = v1.getAllSigs().size();

		Collection<Sig> sigs = new ModuleMerger().mergeSigs(v1, one);

		assertEquals(sigNum + 1, sigs.size());

		sigs = new ModuleMerger().mergeSigs(one, v1);

		assertEquals(sigNum + 1, sigs.size());
	}

	@Test
	public void mergeSigNamesTest() throws Exception {
		Files.find(Paths.get("misc"), Integer.MAX_VALUE, (filePath, fileAttr) -> fileAttr.isRegularFile())
				.forEach(p1 -> {
					try {
						Files.find(Paths.get("misc"), Integer.MAX_VALUE,
								(filePath, fileAttr) -> fileAttr.isRegularFile()).forEach(p2 -> mergeSigNames(p1, p2));
					} catch (IOException e) {
						e.printStackTrace();
						fail();
					}
				});
	}

	private void mergeSigNames(Path p1, Path p2) {
		Module v1 = CompUtil.parseEverything_fromFile(rep, null, p1.toString());
		Module v2 = CompUtil.parseEverything_fromFile(rep, null, p2.toString());

		Set<String> allNames = getSigNames(v1.getAllSigs());
		allNames.addAll(getSigNames(v2.getAllSigs()));

		Set<String> mergedNames = getSigNames(new ModuleMerger().mergeSigs(v1, v2));
		assertEquals(allNames, mergedNames);
	}

	private Set<String> getSigNames(Iterable<Sig> allSigs) {
		Set<String> names = new HashSet<String>();
		for (Sig s : allSigs) {
			names.add(s.label);
		}
		return names;
	}

}
