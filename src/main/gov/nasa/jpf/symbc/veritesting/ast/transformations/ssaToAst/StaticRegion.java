package gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst;

import com.ibm.wala.ssa.IR;
import gov.nasa.jpf.symbc.veritesting.ast.def.Region;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;

import java.util.*;


public class StaticRegion implements Region{
    public final Stmt staticStmt;
    public final IR ir;
    public final StackSlotTable stackSlotTable;
    public final OutputTable outputTable; //slot -> var

    public StaticRegion(Stmt staticStmt, IR ir){
        this.staticStmt = staticStmt;
        this.ir  = ir;
        stackSlotTable = new StackSlotTable(ir);
        outputTable = new OutputTable(stackSlotTable);

    }


}
