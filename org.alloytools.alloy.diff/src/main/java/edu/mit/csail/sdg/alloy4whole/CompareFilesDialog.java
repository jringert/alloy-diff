package edu.mit.csail.sdg.alloy4whole;

import static edu.mit.csail.sdg.alloy4.A4Preferences.FontName;
import static edu.mit.csail.sdg.alloy4.A4Preferences.FontSize;
import static edu.mit.csail.sdg.alloy4.A4Preferences.TabSize;

import java.awt.Component;
import java.awt.Container;
import java.awt.Font;
import java.awt.GraphicsEnvironment;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import javax.swing.AbstractListModel;
import javax.swing.BorderFactory;
import javax.swing.BoxLayout;
import javax.swing.ComboBoxModel;
import javax.swing.JButton;
import javax.swing.JComboBox;
import javax.swing.JComponent;
import javax.swing.JDialog;
import javax.swing.JEditorPane;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JPanel;
import javax.swing.SwingUtilities;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;
import javax.swing.plaf.basic.BasicComboBoxRenderer;

import org.alloytools.alloy.diff.ModuleMerger;

import edu.mit.csail.sdg.alloy4.A4Preferences.ChoicePref;
import edu.mit.csail.sdg.alloy4.A4Preferences.Pref;
import edu.mit.csail.sdg.alloy4.A4Preferences.StringChoicePref;
import edu.mit.csail.sdg.alloy4.OurDialog;
import edu.mit.csail.sdg.alloy4.OurSyntaxWidget;
import edu.mit.csail.sdg.alloy4.OurUtil;
import edu.mit.csail.sdg.alloy4.OurUtil.GridBagConstraintsBuilder;

@SuppressWarnings({ "serial" })
public class CompareFilesDialog extends JDialog {

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
	private static SwingLogPanel log = null;

	private List<OurSyntaxWidget> tabsList;

	public CompareFilesDialog(SwingLogPanel log, String binary, List<OurSyntaxWidget> list, String currentViewFile) {
		this.log = log;
		this.binary = binary;
		this.tabsList = list;
		this.currentViewFile = currentViewFile;
		// this.setResizable(false);
		if (log != null && binary != null) {
		}
		initUI();
	}

	protected final void initUI() {
		// setResizable(false);
		JLabel dialogLabel = new JLabel();
		dialogLabel.setText("Compare Alloy Models by computing differences.");

		dialogLabel.setFont(new Font(FontName.get(), Font.PLAIN, FontSize.get()));
		;

		ArrayList<String> tabListNames = new ArrayList<String>();
		int currentIndex = 0;
		HashMap<Integer, String> fileMap = new HashMap<Integer, String>();
		for (OurSyntaxWidget tab : tabsList) {
			fileMap.put(currentIndex, tab.getFilename());
			currentIndex++;
			tabListNames.add(tab.getFilename().substring(tab.getFilename().lastIndexOf('\\') + 1));
		}

		StringChoicePref tabNamesLeft = new StringChoicePref("LeftFile", "Find instances of ", tabListNames);
		StringChoicePref tabNamesRight = new StringChoicePref("RightFile", "that are not instances of", tabListNames);

		JButton compareButton = new JButton("Compute Diff");

		tabNamesLeft.set(currentViewFile.substring(currentViewFile.lastIndexOf('\\') + 1));
		tabNamesRight.setSelectedIndex(0);

		add(makeGrid(dialogLabel, mkCombo(tabNamesLeft), mkCombo(tabNamesRight), mkButton(compareButton)));

		setTitle("Semantic Difference of Alloy Models");

		pack();
		setSize(getSize().width + 5, getSize().height + 5);
		setResizable(true);
		setLocationRelativeTo(null);
		setAlwaysOnTop(false);

		CompareFilesDialog dialog = this;
		compareButton.addActionListener(new ActionListener() {

			@Override
			public void actionPerformed(ActionEvent e) {

				Compare.CompareModules(fileMap.get(tabNamesLeft.getSelectedIndex()),
						fileMap.get(tabNamesRight.getSelectedIndex()), log);
				dialog.dispose();
			}
		});
	}

	public static JPanel makeGrid(Container label, Container comboLeft, Container comboRight, Container buttonCompare) {
		JPanel ans = new JPanel(new GridBagLayout());
		GridBagConstraints gbc = new GridBagConstraints();

		ans.setBorder(BorderFactory.createEmptyBorder(5, 5, 5, 5));

		gbc.insets = new Insets(5, 5, 5, 5);

		gbc.fill = GridBagConstraints.HORIZONTAL;
		gbc.gridx = 0;
		gbc.gridy = 0;
		ans.add(label, gbc);

		gbc.fill = GridBagConstraints.HORIZONTAL;
		gbc.gridx = 0;
		gbc.gridy = 1;
		ans.add(comboLeft, gbc);

		gbc.fill = GridBagConstraints.HORIZONTAL;
		gbc.gridx = 0;
		gbc.gridy = 3;
		ans.add(comboRight, gbc);

		gbc.fill = GridBagConstraints.HORIZONTAL;
		gbc.gridx = 0;
		gbc.gridy = 4;
		// gbc.gridwidth = 2;
		ans.add(buttonCompare, gbc);

		return ans;
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
