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

    //SH: this is the last instruction where SPF needs to start from after the region
    public final int endIns;

    //SH: this is the region input. slot -> var
    public final InputTable inputTable;

    public StaticRegion(Stmt staticStmt, IR ir, int endIns){
        this.staticStmt = staticStmt;
        this.ir  = ir;
        stackSlotTable = new StackSlotTable(ir);
        outputTable = new OutputTable(stackSlotTable);
        inputTable = new InputTable(ir, stackSlotTable, staticStmt);
        this.endIns = endIns;

    }


}
