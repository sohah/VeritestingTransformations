package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAPhiInstruction;
import com.ibm.wala.ssa.SymbolTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StackSlotIVisitor;
import za.ac.sun.cs.green.expr.Expression;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;

// MWW: TODO Soha & Vaibhav: add functions to retrieve SPF information from Region -
//      TODO This is something we will want to do repeatedly.
//      TODO What kinds of information do you think we will want?
//      TODO    Stack slot type?
//      TODO    ???
//
// MWW: TODO Do we need a separate map for this, or should we pass in some
//      TODO SPF context to grab it?
//


public interface Region {

}
