package gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution;

import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.OutputTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StackSlotTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticRegion;

public class DynamicRegion extends StaticRegion {

    public static int uniqueCounter = 0;
    private Stmt dynStmt;
    private VarTypeTable varTypeTable;
    private ValueSymbolTable valueSymbolTable;
    private StackSlotTable stackSlotTb;
    private OutputTable outputTb;


    public DynamicRegion(StaticRegion staticRegion) {
        super(staticRegion.getStaticStmt(), staticRegion.ir);
        valueSymbolTable = new ValueSymbolTable(ir);
        varTypeTable = new VarTypeTable();
        dynStmt = null;
    }


    public void setDynStmt(Stmt dynStmt) {
        this.dynStmt = dynStmt;
    }

    public ValueSymbolTable getValueSymbolTable() {
        return valueSymbolTable;
    }

    public Table<String> getVarTypeTable() {
        return varTypeTable;
    }

    public Stmt getDynStmt() {
        return dynStmt;
    }

    @Override
    public StackSlotTable getStackSlotTable(){
        return stackSlotTb;
    }

    @Override
    public OutputTable getOutputTable(){
        return outputTb;
    }

}
