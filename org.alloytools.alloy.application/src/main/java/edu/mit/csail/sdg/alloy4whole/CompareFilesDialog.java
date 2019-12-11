package edu.mit.csail.sdg.alloy4whole;

import java.awt.Component;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
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

import org.alloytools.alloy.diff.ModuleMerger;

import edu.mit.csail.sdg.alloy4.A4Preferences.ChoicePref;
import edu.mit.csail.sdg.alloy4.A4Preferences.Pref;
import edu.mit.csail.sdg.alloy4.A4Preferences.StringChoicePref;
import edu.mit.csail.sdg.alloy4.OurBorder;
import edu.mit.csail.sdg.alloy4.OurSyntaxWidget;
import edu.mit.csail.sdg.alloy4.OurTabbedSyntaxWidget;
import edu.mit.csail.sdg.alloy4.OurUtil;
import edu.mit.csail.sdg.alloy4.OurUtil.GridBagConstraintsBuilder;

@SuppressWarnings({
                   "serial"
} )
public class CompareFilesDialog extends JFrame {

    private JEditorPane tab;

    @SuppressWarnings("unchecked" )
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

    private OurTabbedSyntaxWidget text;

    private static class BRModel<T> implements BoundedRangeModel {

        private final ChoicePref<T> pref;

        public BRModel(ChoicePref<T> pref) {
            this.pref = pref;
        }

        @Override
        public int getMinimum() {
            return 0;
        }

        @Override
        public int getMaximum() {
            return pref.validChoices().size() - 1;
        }

        @Override
        public int getValue() {
            return pref.getSelectedIndex();
        }

        @Override
        public int getExtent() {
            return 0;
        }

        @Override
        public void setValueIsAdjusting(boolean b) {
        }

        @Override
        public boolean getValueIsAdjusting() {
            return false;
        }

        @Override
        public void setRangeProperties(int value, int extent, int min, int max, boolean adjusting) {
            throw new UnsupportedOperationException();
        }

        @Override
        public void addChangeListener(ChangeListener x) {
            pref.addChangeListener(x);
        }

        @Override
        public void removeChangeListener(ChangeListener x) {
            pref.removeChangeListener(x);
        }

        @Override
        public void setValue(int n) {
            if (n >= getMinimum() && n <= getMaximum())
                pref.setSelectedIndex(n);
        }

        @Override
        public void setExtent(int n) {
            throw new UnsupportedOperationException();
        }

        @Override
        public void setMinimum(int n) {
            throw new UnsupportedOperationException();
        }

        @Override
        public void setMaximum(int n) {
            throw new UnsupportedOperationException();
        }
    }

    private abstract class CBRenderer extends BasicComboBoxRenderer {

        @Override
        public Component getListCellRendererComponent(JList list, Object value, int index, boolean isSelected, boolean cellHasFocus) {
            return super.getListCellRendererComponent(list, render(value), index, isSelected, cellHasFocus);
        }

        protected abstract Object render(Object value);
    }

    private final Map<Pref< ? >,JComponent> pref2comp = new HashMap<Pref< ? >,JComponent>();
    private final String                    binary;
    private final SwingLogPanel             log;

    private List<OurSyntaxWidget>           tabsList;

    public CompareFilesDialog(SwingLogPanel log, String binary, List<OurSyntaxWidget> list) {
        this.log = log;
        this.binary = binary;
        this.tabsList = list;
        if (log != null && binary != null) {
        }
        initUI();
    }

    protected final void initUI() {

        ArrayList<String> tabListNames = new ArrayList<String>();
        for (OurSyntaxWidget tab : tabsList) {
            tabListNames.add(tab.getFilename());
        }

        StringChoicePref tabNamesLeft = new StringChoicePref("LeftFile", "Left File", tabListNames);
        StringChoicePref tabNamesRight = new StringChoicePref("RightFile", "Right File", tabListNames);

        JButton compareButton = new JButton("Compare");

        JPanel p = OurUtil.makeGrid(2, gbc().make(), mkCombo(tabNamesLeft), mkCombo(tabNamesRight), mkButton(compareButton));

        this.tab = new JEditorPane();

        //tab.addTab("", initEditorPane());
        //tab.addTab("Solver", initSolverPane());
        //tab.addTab("Miscellaneous", initMiscPane());

        add(p);
        //add(mkCombo(tabNamesRight));

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
                //dispose();
            }
        });
    }

    @SuppressWarnings({
                       "unchecked"
    } )
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

    private <T> ComboBoxModel mkComboBoxModelFor(ChoicePref<T> pref) {
        return new CBModel<T>(pref);
    }

    private <T extends JComponent> T make(T comp) {
        return OurUtil.make(comp);
    }


    private Component makeTabPane(JPanel pane) {
        JPanel p = new JPanel(new GridBagLayout());
        // pane.setBorder(new OurBorder(true, true, true, true));
        p.add(pane, gbc().pos(0, 0).fill(GridBagConstraints.BOTH).insets(new Insets(5, 5, 5, 5)).anchor(GridBagConstraints.NORTH).make());
        p.add(new JLabel(), gbc().pos(0, 1).weighty(1).fill(GridBagConstraints.BOTH).make());
        JPanel ans = OurUtil.make(p, new OurBorder(true, true, true, true));
        return ans;
    }

    private GridBagConstraintsBuilder gbc() {
        GridBagConstraintsBuilder ans = new GridBagConstraintsBuilder();
        ans.anchor(GridBagConstraints.WEST).insets(new Insets(3, 3, 3, 3)).ipads(3, 3).fill(GridBagConstraints.BOTH);
        return ans;
    }

    public static void logPrefChanged(SwingLogPanel log, Pref< ? > pref) {
        if (log == null)
            return;
        log.log("Option ");
        log.logBold(pref.title);
        log.log(" changed to ");
        log.logBold(pref.get() + "\n");
        log.flush();
    }

    public static void logOnChange(final SwingLogPanel log, final Pref< ? >... prefs) {
        if (log == null)
            return;
        for (final Pref< ? > pref : prefs) {
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
                CompareFilesDialog sd = new CompareFilesDialog(null, null, null);
                sd.setDefaultCloseOperation(EXIT_ON_CLOSE);
                sd.setVisible(true);
            }
        });
    }

}
