package gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst;

import com.ibm.wala.ssa.IR;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import gov.nasa.jpf.symbc.veritesting.ast.def.Region;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.*;


public class StaticRegion implements Region {
    public final Stmt staticStmt;
    public final IR ir;
    public final SlotParamTable slotParamTable;
    public final OutputTable outputTable;

    //SH: this is the last instruction where SPF needs to start from after the region
    public final int endIns;
    public final boolean isMethodRegion;

    //SH: this is the region input. slot/param -> var
    public final InputTable inputTable;
    public final VarTypeTable varTypeTable;

    public StaticRegion(Stmt staticStmt, IR ir, Boolean isMethodRegion, int endIns) {
        this.staticStmt = staticStmt;
        this.ir = ir;
        this.isMethodRegion = isMethodRegion;

        Pair<Integer, Integer> regionBoundaries = computeRegionBoundaries(staticStmt);
        Integer firstUse = regionBoundaries.getFirst(); // first use var that hasn't been defined in the region
        Integer lastDef = regionBoundaries.getSecond();

        if(isMethodRegion){
            slotParamTable = new SlotParamTable(ir, isMethodRegion, staticStmt);
            varTypeTable = new VarTypeTable(ir);
        }
        else{
            slotParamTable = new SlotParamTable(ir, isMethodRegion, staticStmt, new Pair<>(firstUse, lastDef));
            varTypeTable = new VarTypeTable(ir, new Pair<>(firstUse, lastDef));
        }
        inputTable = new InputTable(ir, isMethodRegion, slotParamTable, staticStmt);
        outputTable = new OutputTable(ir, isMethodRegion, slotParamTable, inputTable, staticStmt);
        this.endIns = endIns;
    }

    public boolean isVoidMethod(){
        return this.outputTable.table.size() == 0;
    }

    private Pair<Integer, Integer> computeRegionBoundaries(Stmt stmt) {
        ExprBoundaryVisitor exprBoundaryVisitor = new ExprBoundaryVisitor();

        RegionBoundaryVisitor regionBoundaryVisitor = new RegionBoundaryVisitor(exprBoundaryVisitor);
        stmt.accept(regionBoundaryVisitor);
        return new Pair<>(regionBoundaryVisitor.getFirstUse(), regionBoundaryVisitor.getLastDef());
    }
}
