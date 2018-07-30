package gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst;

import com.ibm.wala.ssa.IR;
import gov.nasa.jpf.symbc.veritesting.ast.def.Region;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;


public class StaticRegion implements Region {
    public final Stmt staticStmt;
    public final IR ir;
    public final SlotParamTable slotParamTable;
    public final OutputTable outputTable;

    //SH: this is the last instruction where SPF needs to start from after the region
    public final int endIns;
    public final boolean isMethodRegion;

    //SH: this is the region input. slot -> var
    public final InputTable inputTable;

    public StaticRegion(Stmt staticStmt, IR ir, Boolean isMethodRegion, int endIns) {
        this.staticStmt = staticStmt;
        this.ir = ir;
        this.isMethodRegion = isMethodRegion;
        slotParamTable = new SlotParamTable(ir, isMethodRegion);
        inputTable = new InputTable(ir, isMethodRegion, slotParamTable, staticStmt);
        outputTable = new OutputTable(ir, isMethodRegion, slotParamTable, inputTable);
        this.endIns = endIns;
    }

    public boolean isVoidMethod(){
        return this.outputTable.table.size() == 0;
    }
}
