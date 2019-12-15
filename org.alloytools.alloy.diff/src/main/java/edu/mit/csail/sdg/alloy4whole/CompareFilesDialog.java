package edu.mit.csail.sdg.alloy4whole;

import java.awt.Component;
import java.awt.Font;
import java.awt.GridBagConstraints;
import java.awt.Insets;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import javax.swing.AbstractListModel;
import javax.swing.BoundedRangeModel;
import javax.swing.ComboBoxModel;
import javax.swing.JButton;
import javax.swing.JComboBox;
import javax.swing.JComponent;
import javax.swing.JEditorPane;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JPanel;
import javax.swing.SwingUtilities;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;
import javax.swing.plaf.basic.BasicComboBoxRenderer;
import javax.swing.text.StyledEditorKit.FontSizeAction;

import org.alloytools.alloy.diff.ModuleMerger;

import edu.mit.csail.sdg.alloy4.A4Preferences.ChoicePref;
import edu.mit.csail.sdg.alloy4.A4Preferences.Pref;
import edu.mit.csail.sdg.alloy4.A4Preferences.StringChoicePref;
import edu.mit.csail.sdg.alloy4.OurDialog;
import edu.mit.csail.sdg.alloy4.OurSyntaxWidget;
import edu.mit.csail.sdg.alloy4.OurTabbedSyntaxWidget;
import edu.mit.csail.sdg.alloy4.OurUtil;
import edu.mit.csail.sdg.alloy4.OurUtil.GridBagConstraintsBuilder;
import static edu.mit.csail.sdg.alloy4.A4Preferences.AnalyzerHeight;
import static edu.mit.csail.sdg.alloy4.A4Preferences.AnalyzerWidth;
import static edu.mit.csail.sdg.alloy4.A4Preferences.AnalyzerX;
import static edu.mit.csail.sdg.alloy4.A4Preferences.AnalyzerY;
import static edu.mit.csail.sdg.alloy4.A4Preferences.AntiAlias;
import static edu.mit.csail.sdg.alloy4.A4Preferences.AutoVisualize;
import static edu.mit.csail.sdg.alloy4.A4Preferences.CoreGranularity;
import static edu.mit.csail.sdg.alloy4.A4Preferences.CoreMinimization;
import static edu.mit.csail.sdg.alloy4.A4Preferences.FontName;
import static edu.mit.csail.sdg.alloy4.A4Preferences.FontSize;
import static edu.mit.csail.sdg.alloy4.A4Preferences.ImplicitThis;
import static edu.mit.csail.sdg.alloy4.A4Preferences.InferPartialInstance;
import static edu.mit.csail.sdg.alloy4.A4Preferences.LAF;
import static edu.mit.csail.sdg.alloy4.A4Preferences.Model0;
import static edu.mit.csail.sdg.alloy4.A4Preferences.Model1;
import static edu.mit.csail.sdg.alloy4.A4Preferences.Model2;
import static edu.mit.csail.sdg.alloy4.A4Preferences.Model3;
import static edu.mit.csail.sdg.alloy4.A4Preferences.NoOverflow;
import static edu.mit.csail.sdg.alloy4.A4Preferences.RecordKodkod;
import static edu.mit.csail.sdg.alloy4.A4Preferences.SkolemDepth;
import static edu.mit.csail.sdg.alloy4.A4Preferences.Solver;
import static edu.mit.csail.sdg.alloy4.A4Preferences.SubMemory;
import static edu.mit.csail.sdg.alloy4.A4Preferences.SubStack;
import static edu.mit.csail.sdg.alloy4.A4Preferences.SyntaxDisabled;
import static edu.mit.csail.sdg.alloy4.A4Preferences.TabSize;
import static edu.mit.csail.sdg.alloy4.A4Preferences.Unrolls;
import static edu.mit.csail.sdg.alloy4.A4Preferences.VerbosityPref;
import static edu.mit.csail.sdg.alloy4.A4Preferences.WarningNonfatal;
import static edu.mit.csail.sdg.alloy4.A4Preferences.Welcome;


@SuppressWarnings({ "serial" })
public class CompareFilesDialog extends JFrame {

	@SuppressWarnings("unchecked")
	private static class CBModel<T> extends AbstractListModel implements ComboBoxModel {

		private final ChoicePref<T> pref;

		public CBModel(final ChoicePref<T> pref) {
			this.pref = pref;
			this.pref.addChangeListener(new ChangeListener() {

				@Override
				public void stateChanged(ChangeEvent e) {
					fireContentsChanged(pref, -1, -1);
				}
			});
		}

		@Override
		public int getSize() {
			return pref.validChoices().size();
		}

		@Override
		public Object getElementAt(int index) {
			return pref.validChoices().get(index);
		}

		@Override
		public void setSelectedItem(Object anItem) {
			pref.set((T) anItem);
		}

		@Override
		public Object getSelectedItem() {
			return pref.get();
		}
	}

	private abstract class CBRenderer extends BasicComboBoxRenderer {

		@Override
		public Component getListCellRendererComponent(JList list, Object value, int index, boolean isSelected,
				boolean cellHasFocus) {
			return super.getListCellRendererComponent(list, render(value), index, isSelected, cellHasFocus);
		}

		protected abstract Object render(Object value);
	}

	private final Map<Pref<?>, JComponent> pref2comp = new HashMap<Pref<?>, JComponent>();
	private final String binary;
	private final String currentViewFile;
	private final SwingLogPanel log;

	private List<OurSyntaxWidget> tabsList;

	public CompareFilesDialog(SwingLogPanel log, String binary, List<OurSyntaxWidget> list, String currentViewFile) {
		this.log = log;
		this.binary = binary;
		this.tabsList = list;
		this.currentViewFile = currentViewFile;
		if (log != null && binary != null) {
		}
		initUI();
	}

	protected final void initUI() {

		JLabel dialogLabel = new JLabel();
		dialogLabel.setText("Find instances of Right file that are not instances of Left file");
		//dialogLabel.setFont(new Font("Courier", Font.BOLD,12));
		
		ArrayList<String> tabListNames = new ArrayList<String>();
		for (OurSyntaxWidget tab : tabsList) {
			//tabListNames.add(tab.getFilename());
			tabListNames.add(tab.getFilename().substring(tab.getFilename().lastIndexOf('\\') + 1));
		}

		StringChoicePref tabNamesLeft = new StringChoicePref("LeftFile", "Left File", tabListNames);
		StringChoicePref tabNamesRight = new StringChoicePref("RightFile", "Right File", tabListNames);

		JButton compareButton = new JButton("Compare");

		tabNamesLeft.set(currentViewFile);
		tabNamesRight.setSelectedIndex(0);

		JPanel p = OurUtil.makeGrid(2, gbc().make(), mkCombo(tabNamesLeft),
				mkCombo(tabNamesRight), mkButton(compareButton));

		new JEditorPane();

		add(p);
		//add(dialogLabel);
		// add(mkCombo(tabNamesRight));

		setTitle("Compare Alloy Models");
		
		pack();
		setSize(getSize().width + 5, getSize().height + 5);
		setResizable(false);
		setLocationRelativeTo(null);
		setAlwaysOnTop(false);

		compareButton.addActionListener(new ActionListener() {

			@Override
			public void actionPerformed(ActionEvent e) {
				ModuleMerger m = new ModuleMerger(tabNamesLeft.get(), tabNamesRight.get());
				// dispose();
			}
		});
	}

	@SuppressWarnings({ "unchecked" })
	protected <T> JPanel mkCombo(final ChoicePref<T> pref) {
		JComboBox cb = make(new JComboBox(mkComboBoxModelFor(pref)));
		pref2comp.put(pref, cb);
		cb.setRenderer(new CBRenderer() {

			@Override
			protected Object render(Object value) {
				return pref.renderValueShort((T) value);
			}
		});
		return OurUtil.makeH(pref.title + ": ", cb);
	}

	protected <T> JPanel mkButton(JButton jb) {
		return OurUtil.makeH(null, jb, null);
	}
	
	protected <T> JPanel mkLabel(JLabel l) {
		return OurUtil.makeH(null, l, null);
	}
	
	private <T> ComboBoxModel mkComboBoxModelFor(ChoicePref<T> pref) {
		return new CBModel<T>(pref);
	}

	private <T extends JComponent> T make(T comp) {
		return OurUtil.make(comp);
	}

	private GridBagConstraintsBuilder gbc() {
		GridBagConstraintsBuilder ans = new GridBagConstraintsBuilder();
		ans.anchor(GridBagConstraints.WEST).insets(new Insets(3, 3, 3, 3)).ipads(3, 3).fill(GridBagConstraints.BOTH);
		return ans;
	}

	public static void logPrefChanged(SwingLogPanel log, Pref<?> pref) {
		if (log == null)
			return;
		log.log("Option ");
		log.logBold(pref.title);
		log.log(" changed to ");
		log.logBold(pref.get() + "\n");
		log.flush();
	}

	public static void logOnChange(final SwingLogPanel log, final Pref<?>... prefs) {
		if (log == null)
			return;
		for (final Pref<?> pref : prefs) {
			pref.addChangeListener(new ChangeListener() {

				@Override
				public void stateChanged(ChangeEvent e) {
					logPrefChanged(log, pref);
				}
			});
		}
	}

	public static void main(String[] args) {
		SwingUtilities.invokeLater(new Runnable() {

			@Override
			public void run() {
				CompareFilesDialog sd = new CompareFilesDialog(null, null, null, null);
				sd.setDefaultCloseOperation(EXIT_ON_CLOSE);
				sd.setVisible(true);
			}
		});
	}

}
