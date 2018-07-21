package gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution;

import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.ValueSymbolTable;

public class DynamicRegion extends StaticRegion {

    private ValueSymbolTable valueSymbolTable;
    private Stmt dynStmt;

    public DynamicRegion(StaticRegion staticRegion) {
        super(staticRegion.getStaticStmt(), staticRegion.ir);
        valueSymbolTable = new ValueSymbolTable(ir);
        dynStmt = null;
    }


    public void setDynStmt(Stmt dynStmt) {
        this.dynStmt = dynStmt;
    }

    public ValueSymbolTable getValueSymbolTable() {
        return valueSymbolTable;
    }


    public Stmt getDynStmt() {
        return dynStmt;
    }
}
