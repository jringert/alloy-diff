package edu.mit.csail.sdg.alloy4whole;

import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;

import javax.swing.JMenu;

import org.alloytools.alloy.diff.ModuleDiff;

import edu.mit.csail.sdg.alloy4viz.VizGUI;
import edu.mit.csail.sdg.translator.A4Solution;

public class Compare {

	private static final String ALLOY_EXAMPLE_OUTPUT_XML = "alloy_example_output.xml";
	public static A4Solution ans;
	public static VizGUI viz;

	public static void CompareModules(String leftFile, String rightFile, SwingLogPanel log) {
		if (log != null) {
			log.clearError();
			log.logDivider();

			log.logBold("Comparing: " + leftFile.substring(leftFile.lastIndexOf('\\') + 1) + " with "
					+ rightFile.substring(rightFile.lastIndexOf('\\') + 1));

		}
		
		ans = ModuleDiff.diff(leftFile, rightFile);

		if (ans.satisfiable()) {
			ans.writeXML("alloy_compare_output.xml");
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
