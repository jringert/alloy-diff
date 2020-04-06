package org.alloytools.alloy.flatten;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import javax.swing.JFrame;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.Listener;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.SafeList;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;

/**
 * THis is a module to hold flattened signatures and constraints
 * 
 * Alloy doesn't support reuse of CompModule well.
 * 
 * @author ringert
 *
 */
public class FlatModule implements Module {
	
	private List<Sig> signatures;

	private String modelName;
	private Pos pos;

	@Override
	public Pos pos() {
		return pos;
	}

	public void setPos(Pos pos) {
		this.pos = pos;
	}

	@Override
	public String path() {
		return path;
	}

	public void setPath(String path) {
		this.path = path;
	}

	public String getModelName() {
		return modelName;
	}

	private String path;

	@Override
	public String explain() {
		return "this is a generated, virtual module";
	}

	@Override
	public SafeList<? extends Module> getAllReachableModules() {
		SafeList<Module> modules = new SafeList<>();
		modules.add(this);
		return modules;
	}

	@Override
	public List<String> getAllReachableModulesFilenames() {
		List<String> fns = new ArrayList<>(1);
		fns.add(path);
		return fns;
	}

	@Override
	public ConstList<Sig> getAllReachableSigs() {
		// FIXME check that this is correct
		return ConstList.make(signatures);
	}

	@Override
	public ConstList<Sig> getAllReachableUserDefinedSigs() {
		return ConstList.make(signatures);
	}

	@Override
	public SafeList<Sig> getAllSigs() {
		SafeList<Sig> sigs = new SafeList<>(signatures.size());
		sigs.addAll(signatures);
		return sigs;
	}

	@Override
	public SafeList<Func> getAllFunc() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public ConstList<Pair<String, Expr>> getAllAssertions() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SafeList<Pair<String, Expr>> getAllFacts() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Expr getAllReachableFacts() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public ConstList<Command> getAllCommands() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void addGlobal(String name, Expr value) {
		// TODO Auto-generated method stub

	}

	@Override
	public JFrame showAsTree(Listener listener) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Expr parseOneExpressionFromString(String input) throws Err, FileNotFoundException, IOException {
		// TODO Auto-generated method stub
		return null;
	}

	public void setModelName(String modelName) {
		this.modelName = modelName;
	}

}
