package edu.mit.csail.sdg.alloy4whole;

import java.awt.BorderLayout;
import java.awt.FlowLayout;
import java.awt.Font;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.util.Collection;

import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JTextArea;
import javax.swing.JTextPane;
import javax.swing.text.Style;
import javax.swing.text.StyleConstants;
import javax.swing.text.StyledDocument;

import org.alloytools.alloy.diff.ModuleMerger;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.OurAntiAlias;
import edu.mit.csail.sdg.alloy4.OurUtil;
import edu.mit.csail.sdg.alloy4viz.VizGUI;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

public class Compare {

	public static void CompareModules(String leftFile, String rightFile, SwingLogPanel log) {
		if (log != null) {
			log.clearError();
			log.logDivider();

			log.logBold("Comparing: " + leftFile.substring(leftFile.lastIndexOf('\\') + 1) + " with "
					+ rightFile.substring(rightFile.lastIndexOf('\\') + 1));

		}
		// TODO Auto-generated method stub
		VizGUI viz = null;

		A4Reporter rep = new A4Reporter() {
			@Override
			public void warning(ErrorWarning msg) {
				System.out.print("Relevance Warning:\n" + (msg.toString().trim()) + "\n\n");
				System.out.flush();
			}
		};

		Module v1, v2;

		v1 = CompUtil.parseEverything_fromFile(rep, null, leftFile);
		v2 = CompUtil.parseEverything_fromFile(rep, null, rightFile);

		// Choose some default options for how you want to execute the
		// commands
		A4Options options = new A4Options();

		options.solver = A4Options.SatSolver.SAT4J;

		Collection<Sig> sigs = ModuleMerger.mergeSigs(v1, v2);

		Command diffCommand = ModuleMerger.generateCommand(v1, v2);

		// Execute the command
		System.out.println("============ Command " + diffCommand + ": ============");
		A4Solution ans = TranslateAlloyToKodkod.execute_command(rep, sigs, diffCommand, options);

		if (ans.satisfiable()) {
			ans.writeXML("alloy_compare_output.xml");
			if (log != null) {
				log.logLink("\nInstance Found", "alloy_compare_output.xml");
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
		log.logDivider();
		log.flush();
		// showViz(viz, ans);
	}

	private static void showViz(A4Solution ans) {
		VizGUI viz = null;

		// If satisfiable...
		if (ans.satisfiable()) {
			// You can query "ans" to find out the values of each set or
			// type.
			// This can be useful for debugging.
			//
			// You can also write the outcome to an XML file
			ans.writeXML("alloy_example_output.xml");
			//
			// You can then visualize the XML file by calling this:
			if (viz == null) {
				viz = new VizGUI(false, "alloy_example_output.xml", null);
			}
		}
	}

}
