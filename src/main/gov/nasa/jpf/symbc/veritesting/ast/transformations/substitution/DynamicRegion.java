package gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution;

import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticRegion;

public class DynamicRegion extends StaticRegion {

    private ValueSymbolTable valueSymbolTable;
    private Stmt dynStmt;
    private static int uniqueCounter;
    private Table<String> varTypeTable;

    public DynamicRegion(StaticRegion staticRegion) {
        super(staticRegion.getStaticStmt(), staticRegion.ir);
        valueSymbolTable = new ValueSymbolTable(ir);
        varTypeTable = new Table<>("var-type table","var", "type");
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


}
