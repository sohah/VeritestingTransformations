package gov.nasa.jpf.symbc.bytecode;

import gov.nasa.jpf.Config;
import gov.nasa.jpf.jvm.ChoiceGenerator;
import gov.nasa.jpf.jvm.ClassInfo;
import gov.nasa.jpf.jvm.DynamicArea;
import gov.nasa.jpf.jvm.ElementInfo;
import gov.nasa.jpf.jvm.FieldInfo;
import gov.nasa.jpf.jvm.Fields;
import gov.nasa.jpf.jvm.KernelState;
import gov.nasa.jpf.jvm.SystemState;
import gov.nasa.jpf.jvm.ThreadInfo;
import gov.nasa.jpf.jvm.bytecode.Instruction;
import gov.nasa.jpf.symbc.SymbolicInstructionFactory;
import gov.nasa.jpf.symbc.heap.HeapChoiceGenerator;
import gov.nasa.jpf.symbc.heap.HeapNode;
import gov.nasa.jpf.symbc.heap.Helper;
import gov.nasa.jpf.symbc.heap.SymbolicInputHeap;
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;
//import gov.nasa.jpf.symbc.uberlazy.TypeHierarchy;

public class ALOAD extends gov.nasa.jpf.jvm.bytecode.ALOAD {

	public ALOAD(int localVarIndex) {
	    super(localVarIndex);
	}

	private HeapNode[] prevSymRefs;
	private ChoiceGenerator<?> prevHeapCG;
	private int numSymRefs = 0;
    private int numNewRefs = 0; // # of new reference objects to account for polymorphism (neha)
    boolean abstractClass = false;

	public Instruction execute (SystemState ss, KernelState ks, ThreadInfo th) {

		Config conf = th.getVM().getConfig();
		String[] lazy = conf.getStringArray("symbolic.lazy");
		if (lazy == null || !lazy[0].equalsIgnoreCase("true"))
			return super.execute(ss,ks,th);

		//neha: check whether the subtypes from polymorphism need to added
		// when instantiating "new" objects during lazy-initialization.
		// the configuration allows to consider all subtypes during the
		// instantiation. In aliasing all subtypes are considered by default.

		// TODO: fix get rid of subtypes

		String subtypes = conf.getString("symbolic.lazy.subtypes", "false");
		//if(!subtypes.equals("false") &&
			//	TypeHierarchy.typeHierarchies == null) {
			//TypeHierarchy.buildTypeHierarchy(th);
		//}

	//	StackFrame sf = th.getTopFrame();
		Object attr = th.getLocalAttr(index);
		String typeOfLocalVar = super.getLocalVariableType();

		if(attr == null || typeOfLocalVar.equals("?")) {
			th.pushLocal(index);
			return getNext(th);
		}
		//if(SymbolicInstructionFactory.debugMode) System.out.println("lazy initialization");
		//int localVar = th.getLocalVariable(index);
		//System.out.println("typeOfLocalVar "+typeOfLocalVar);
		ClassInfo typeClassInfo = ClassInfo.getResolvedClassInfo(typeOfLocalVar);

		//System.out.println(typeClassInfo.getName() + " name of the class");


		int currentChoice;
		ChoiceGenerator<?> thisHeapCG;

		if(!th.isFirstStepInsn()) {
			//System.out.println("the first whatever");

			prevSymRefs = null;
			numSymRefs = 0;
			prevHeapCG = null;

			prevHeapCG = ss.getChoiceGenerator();
			while(!((prevHeapCG == null) || (prevHeapCG instanceof HeapChoiceGenerator))) {
				prevHeapCG = prevHeapCG.getPreviousChoiceGenerator();
			}

			if (prevHeapCG != null) {
				// collect candidates for lazy initialization
				SymbolicInputHeap symInputHeap =
					((HeapChoiceGenerator)prevHeapCG).getCurrentSymInputHeap();

				prevSymRefs = new HeapNode[symInputHeap.count()]; // estimate of size; should be changed
				HeapNode n = symInputHeap.header();
				while (null != n){
					ClassInfo tClassInfo = n.getType();
					if (tClassInfo.isInstanceOf(typeClassInfo)) {

						prevSymRefs[numSymRefs] = n;
						numSymRefs++;
					}
					n = n.getNext();
				}
			}
			int increment = 2;
			if(typeClassInfo.isAbstract()) {
				 abstractClass = true;
				 increment = 1; // only null
			}
			//neha: if subtypes are to be considered
			// TODO fix
//			if(!subtypes.equals("false")) {
//				// get the number of subtypes that exist, and add the number in
//				// the choice generator in addition to the ones that were there
//				numNewRefs = TypeHierarchy.getNumOfElements(typeClassInfo.getName());
//				thisHeapCG = new HeapChoiceGenerator(numSymRefs+increment+numNewRefs); // +null,new
//			} else {
				thisHeapCG = new HeapChoiceGenerator(numSymRefs+increment);  //+null,new
			//}
			ss.setNextChoiceGenerator(thisHeapCG);
			return this;
		} else {
			//this is what returns the results
			thisHeapCG = ss.getChoiceGenerator();
			assert(thisHeapCG instanceof HeapChoiceGenerator) :
				"expected HeapChoiceGenerator, got:" + thisHeapCG;
			currentChoice = ((HeapChoiceGenerator) thisHeapCG).getNextChoice();
		}

		PathCondition pcHeap;
		SymbolicInputHeap symInputHeap;

		if(prevHeapCG == null) {
			pcHeap = new PathCondition();
			symInputHeap = new SymbolicInputHeap();
		} else {
			pcHeap =  ((HeapChoiceGenerator) prevHeapCG).getCurrentPCheap();
			symInputHeap = ((HeapChoiceGenerator) prevHeapCG).getCurrentSymInputHeap();
		}

		assert pcHeap != null;
		assert symInputHeap != null;

		int daIndex = 0; //index into JPF's dynamic area

		if (currentChoice < numSymRefs) { // lazy initialization using a previously lazily initialized object
			HeapNode candidateNode = prevSymRefs[currentChoice];
			// here we should update pcHeap with the constraint attr == candidateNode.sym_v
			pcHeap._addDet(Comparator.EQ, (SymbolicInteger) attr, candidateNode.getSymbolic());
			daIndex = candidateNode.getIndex();
		}
		else if (currentChoice == numSymRefs){ //null object
			pcHeap._addDet(Comparator.EQ, (SymbolicInteger) attr, new IntegerConstant(-1));
			daIndex = -1;
		}
		else if (currentChoice == (numSymRefs + 1) && !abstractClass) {
			//creates a new object with all fields symbolic
			daIndex = Helper.addNewHeapNode(typeClassInfo, th, daIndex, attr, ks, pcHeap,
							symInputHeap, numSymRefs, prevSymRefs);
		} else {
			//TODO: fix subtypes
			System.err.println("subtypes not handled");
//			int counter;
//			if(abstractClass) {
//				counter = currentChoice - (numSymRefs+1) ; //index to the sub-class
//			} else {
//				counter = currentChoice - (numSymRefs+1) - 1;
//			}
//			ClassInfo subClassInfo = TypeHierarchy.getClassInfo(typeClassInfo.getName(), counter);
//			daIndex = Helper.addNewHeapNode(subClassInfo, th, daIndex, attr, ks, pcHeap,
//							symInputHeap, numSymRefs, prevSymRefs);

		}


		th.setLocalVariable(index, daIndex, true);
		th.setLocalAttr(index, null);
		th.push(daIndex, true);

		((HeapChoiceGenerator)thisHeapCG).setCurrentPCheap(pcHeap);
		((HeapChoiceGenerator)thisHeapCG).setCurrentSymInputHeap(symInputHeap);
		if (SymbolicInstructionFactory.debugMode)
			System.out.println("ALOAD pcHeap: " + pcHeap);
		return getNext(th);
	}

}