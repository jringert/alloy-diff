package edu.mit.csail.sdg.alloy4whole;

import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.io.File;
import java.io.IOException;

import javax.swing.JMenu;

import org.alloytools.alloy.diff.Analysis;
import org.alloytools.alloy.diff.ModuleDiff;

import edu.mit.csail.sdg.alloy4viz.VizGUI;
import edu.mit.csail.sdg.translator.A4Solution;

public class Compare {
	
	static {
		try {
			ALLOY_EXAMPLE_OUTPUT_XML = File.createTempFile("alloyInst", ".xml").getAbsolutePath();
		} catch (IOException e) {
			ALLOY_EXAMPLE_OUTPUT_XML = "alloy_example_output.xml";
		}
	}

	private static String ALLOY_EXAMPLE_OUTPUT_XML;
	public static A4Solution ans;
	public static VizGUI viz;

	public static void CompareModules(String leftFile, String rightFile, String analysis, SwingLogPanel log) {
		if (log != null) {
			log.clearError();
			log.logDivider();

			log.logBold("Comparing: " + leftFile.substring(leftFile.lastIndexOf('\\') + 1) + " with "
					+ rightFile.substring(rightFile.lastIndexOf('\\') + 1));

		}
		switch (analysis) {
		case "Semantic Diff":
			ans = ModuleDiff.diff(rightFile, leftFile, -1, true, Analysis.SemDiff);
			break;
		case "Common Instances":
			ans = ModuleDiff.diff(rightFile, leftFile, -1, true, Analysis.CommonInst);
			break;
		case "Equivalence":
			ans = ModuleDiff.diff(rightFile, leftFile, -1, true, Analysis.Equivalence);
			if (ans.satisfiable()) {
				if (log != null) {
					log.logRed("\nNot equivalent.\n Counter-example found. Visualizer opened.\n");
				}
			} else {
				if (log != null) {
					log.log("\nModels are equivalent.\n");
				}
			}
			log.flush();
			showViz(log);
			return;				
		default:
			break;
		}

		if (ans.satisfiable()) {
			if (log != null) {
				log.log("\nInstance Found. Visualizer opened.\n");
			} else {
				System.out.println(ans);
			}
		} else {
			if (log != null) {
				log.logRed(ans + "\n");
			} else {
				System.out.println(ans);
			}
		}

		log.flush();
		showViz(log);
	}

	private static void showViz(SwingLogPanel log) {
		// If satisfiable...
		if (ans.satisfiable()) {
			// You can query "ans" to find out the values of each set or
			// type.
			// This can be useful for debugging.
			//
			// You can also write the outcome to an XML file
			ans.writeXML(ALLOY_EXAMPLE_OUTPUT_XML);
			//

			JMenu m = new JMenu("Next");

			m.addMouseListener(new MouseListener() {

				@Override
				public void mouseReleased(MouseEvent e) {
					// TODO Auto-generated method stub

				}

				@Override
				public void mousePressed(MouseEvent e) {
					Compare.ans = Compare.ans.next();
					if (ans.satisfiable()) {
						ans.writeXML(ALLOY_EXAMPLE_OUTPUT_XML);
						viz.loadXML(ALLOY_EXAMPLE_OUTPUT_XML, true);
						log.log("Next solution displayed.\r\n");
					} else {
						log.log("No more solutions.\r\n");
					}
					log.flush();
				}

				@Override
				public void mouseClicked(MouseEvent arg0) {
					// TODO Auto-generated method stub

				}

				@Override
				public void mouseEntered(MouseEvent arg0) {
					// TODO Auto-generated method stub

				}

				@Override
				public void mouseExited(MouseEvent arg0) {
					// TODO Auto-generated method stub

				}
			});

			// You can then visualize the XML file by calling this:
			viz = new VizGUI(false, ALLOY_EXAMPLE_OUTPUT_XML, m);
		}
	}

}
