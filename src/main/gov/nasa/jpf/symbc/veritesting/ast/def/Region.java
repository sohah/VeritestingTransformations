package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SymbolTable;
import za.ac.sun.cs.green.expr.Expression;

import java.util.Arrays;
import java.util.HashMap;

//SH: stackSlotMap contains the stack slot of every var and for undiscovered stack slots their corresponding var' stack slot will map to -1.

// MWW: TODO Soha & Vaibhav: add functions to retrieve SPF information from Region -
//      TODO This is something we will want to do repeatedly.
//      TODO What kinds of information do you think we will want?
//      TODO    Stack slot type?
//      TODO    ???
//
// MWW: TODO Do we need a separate map for this, or should we pass in some
//      TODO SPF context to grab it?
//


public class Region {
    public final Stmt stmt;
    public final IR ir;
    public final HashMap<Integer, int[]> stackSlotMap;
    // MWW: TODO are all values going to be integers?  Seems unlikely.  Fix this.
    public final HashMap<Expression, Integer> valueMap;

    public Region(Stmt stmt, IR ir,
                  HashMap<Integer, int[]> stackSlotMap,
                  HashMap<Expression, Integer> valueMap) {
        this.stmt = stmt;
        this.ir  = ir;
        this.stackSlotMap = stackSlotMap;
        this.valueMap = valueMap;
    }

    public boolean isConstant(int operand1) {
        SymbolTable table = ir.getSymbolTable();
        return table.isNumberConstant(operand1) ||
                table.isBooleanOrZeroOneConstant(operand1) ||
                table.isNullConstant(operand1);
    }

    public void printStackSlotMap(){
        System.out.println("now printing Stack Slot Map");
        stackSlotMap.forEach((var, stackSlots) -> System.out.println(var + " --------- " + Arrays.toString(stackSlots)));
        System.out.println("end of Stack Slot Map");
    }
}
