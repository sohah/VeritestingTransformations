package gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution;

import com.ibm.wala.ssa.IR;
import gov.nasa.jpf.symbc.veritesting.ast.def.Region;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.OutputTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StackSlotTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticRegion;

public class DynamicRegion implements Region {

    public static int uniqueCounter = 0;
    public final Stmt dynStmt;
    public final VarTypeTable varTypeTable;
    public final ValueSymbolTable valueSymbolTable;
    public final StackSlotTable stackSlotTable;
    public final OutputTable outputTable;
    public final StaticRegion staticRegion;
    public final int endIns;


    public DynamicRegion(StaticRegion staticRegion, Stmt dynStmt, VarTypeTable varTypeTable, ValueSymbolTable valueSymbolTable) {

        this.staticRegion = staticRegion;
        this.dynStmt = dynStmt;
        this.valueSymbolTable = valueSymbolTable;
        this.varTypeTable = varTypeTable;
        this.stackSlotTable = staticRegion.stackSlotTable.clone();
        this.outputTable = staticRegion.outputTable.clone();
        this.endIns = staticRegion.endIns;
    }

    public DynamicRegion(StaticRegion staticRegion, Stmt dynStmt, VarTypeTable varTypeTable, ValueSymbolTable valueSymbolTable, StackSlotTable stackSlotTable, OutputTable outputTable) {
        this.dynStmt = dynStmt;
        this.staticRegion = staticRegion;
        this.varTypeTable = varTypeTable;
        this.valueSymbolTable = valueSymbolTable;
        this.stackSlotTable = stackSlotTable;
        this.outputTable = outputTable;
        this.endIns = staticRegion.endIns;
    }
}
