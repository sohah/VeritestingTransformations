/**
 * 
 */
package gov.nasa.jpf.symbc.realtime.onthefly;

import java.io.FileNotFoundException;
import java.io.PrintStream;

import uppaal.NTA;
import gov.nasa.jpf.Config;
import gov.nasa.jpf.JPF;
import gov.nasa.jpf.PropertyListenerAdapter;
import gov.nasa.jpf.jvm.bytecode.IfInstruction;
import gov.nasa.jpf.search.Search;
import gov.nasa.jpf.symbc.realtime.RealTimeUtils;
import gov.nasa.jpf.symbc.realtime.TimingDocException;
import gov.nasa.jpf.vm.ChoiceGenerator;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.MethodInfo;
import gov.nasa.jpf.vm.ThreadInfo;
import gov.nasa.jpf.vm.VM;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class UppaalOnTheFlyTranslationListener extends PropertyListenerAdapter {
	
	private static final String DEF_OUTPUT_PATH = "./uppaalmodel.xml";
	
	private Config jpfConf;
	private AUPPAALTranslator translator;
	/**
	 * Used for constructing an NTA model amenable to model checking using UPPAAL.
	 * This constructs the TA on the fly as opposed to UppaalTranslationListener, which contains
	 * an intermediate step - the construction of the symbolic execution tree - before translation.
	 * This 'branch' is not maintained.
	 * @param conf
	 * @param jpf
	 */
	public UppaalOnTheFlyTranslationListener(Config conf, JPF jpf) {
		this.jpfConf = conf;
		
		String targetPlatform = this.jpfConf.getString("symbolic.realtime.platform", "").toLowerCase();
		boolean targetTetaSARTS = this.jpfConf.getBoolean("symbolic.realtime.targettetasarts", false);
		switch(targetPlatform) {
			case "jop":
				this.translator = new JOPUPPAALTranslator(this.jpfConf, targetTetaSARTS);
				break;
			case "explicit":
				this.translator = new ExplicitModelUPPAALTranslator(this.jpfConf, targetTetaSARTS);
				break;
			case "timingdoc":
				String timingDocPath = this.jpfConf.getString("symbolic.realtime.timingdocpath");
				if(timingDocPath == null) 
					throw new TimingDocException("symbolic.realtime.timingdocpath has not been set.");
				this.translator = new TimingDocUPPAALTranslator(this.jpfConf, timingDocPath, targetTetaSARTS);
			default:
				System.out.println("Default platform JOP is used");
				this.translator = new JOPUPPAALTranslator(this.jpfConf, targetTetaSARTS);
				break;
		}
	}
	
	@Override
	public void executeInstruction(VM vm, ThreadInfo currentThread, Instruction instructionToExecute) {
		if (!vm.getSystemState().isIgnored()) {
			MethodInfo mi = instructionToExecute.getMethodInfo();
			if(RealTimeUtils.isInSymbolicCallChain(mi, currentThread.getTopFrame(), this.jpfConf)) {
				if(!(instructionToExecute instanceof IfInstruction) ||
				    (instructionToExecute instanceof IfInstruction) &&
					 !currentThread.isFirstStepInsn()) {
					this.translator.translateInstruction(instructionToExecute, currentThread.getTopFrame());
				}
				if(instructionToExecute.getMethodInfo().getLastInsn().equals(instructionToExecute)) {
					this.translator.finalizeAutomatonConstruction(currentThread.getTopFrame());
				}
			}
		}
	}
	
	@Override
	public void searchFinished(Search search) {
		NTA nta = this.translator.finalizeAndGetNTA();
		this.writeNTA(nta);
	}
	
	@Override
	public void choiceGeneratorRegistered(VM vm, ChoiceGenerator<?> nextCG, ThreadInfo currentThread, Instruction executedInstruction) {
		MethodInfo mi = executedInstruction.getMethodInfo();
		if(RealTimeUtils.isInSymbolicCallChain(mi, currentThread.getTopFrame(), this.jpfConf)) {
			this.translator.addChoice(executedInstruction, currentThread.getTopFrame());
		}
	}
	
	@Override
	public void stateBacktracked(Search search) {
		if(RealTimeUtils.isInSymbolicCallChain(search.getVM().getInstruction().getMethodInfo(), search.getVM().getCurrentThread().getTopFrame(), this.jpfConf)) {
			this.translator.backTracked(search.getVM().getInstruction(), search.getVM().getCurrentThread().getTopFrame());
		}
	}
	
	private void writeNTA(NTA nta) {
		String outputPath;
		if(this.jpfConf.getBoolean("symbolic.realtime")) {
			outputPath = this.jpfConf.getString("symbolic.realtime.outputpath");
			assert outputPath != null;
		} else
			outputPath = UppaalOnTheFlyTranslationListener.DEF_OUTPUT_PATH;
		
		PrintStream ps = null;
		try {
			ps = new PrintStream(outputPath);
		} catch (FileNotFoundException e) {
			System.err.println(e.getMessage());
			System.err.println("Defaulting to output path: " + UppaalOnTheFlyTranslationListener.DEF_OUTPUT_PATH);
			outputPath = UppaalOnTheFlyTranslationListener.DEF_OUTPUT_PATH;
		}
		nta.writeXMLWithPrettyLayout(ps);
	}
}
