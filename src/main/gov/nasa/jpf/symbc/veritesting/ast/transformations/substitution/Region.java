package gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution;

import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAPhiInstruction;
import com.ibm.wala.ssa.SymbolTable;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import za.ac.sun.cs.green.expr.Expression;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;

public class Region {
    private Stmt stmt;
    private final IR ir;
    private StackSlotTable stackSlotTable;
    private ValueSymbolTable valueSymbolTable;

    public Region(Stmt stmt, IR ir){
        this.stmt = stmt;
        this.ir  = ir;
        stackSlotTable = new StackSlotTable(ir);
        this.valueSymbolTable = new ValueSymbolTable(ir);
    }

    public StackSlotTable getStackSlotTable() {
        return stackSlotTable;
    }

    public ValueSymbolTable getValueSymbolTable() {
        return valueSymbolTable;
    }

    public void setValueSymbolTable(ValueSymbolTable valueSymbolTable) {
        this.valueSymbolTable = valueSymbolTable;
    }

    public void setStmt(Stmt stmt){
        this.stmt = stmt;
    }

    public Stmt getStmt() {
        return stmt;
    }
}
