package gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment;

import gov.nasa.jpf.symbc.veritesting.ast.def.Region;
import gov.nasa.jpf.symbc.veritesting.ast.def.SPFCaseStmt;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticRegion;

import java.util.HashSet;

public class DynamicRegion implements Region {

    public static int uniqueCounter = 0;
    public final Stmt dynStmt;
    public final SlotTypeTable slotTypeTable;
    public final SlotParamTable slotParamTable;
    public final OutputTable outputTable;
    public final StaticRegion staticRegion;
    public final Table.VarTypeTable varTypeTable;
    public final int endIns;
    public final boolean isMethodRegion;
    public final HashSet<SPFCaseStmt> spfCaseSet;


    //SH: used for the first construction of the DynamicRegion out of a StaticRegion.
    public DynamicRegion(StaticRegion staticRegion,
                         Stmt dynStmt,
                         SlotTypeTable slotTypeTable,
                         HashSet<SPFCaseStmt> spfCaseSet) {

        this.staticRegion = staticRegion;
        this.dynStmt = dynStmt;
        this.slotTypeTable = slotTypeTable;
        this.slotParamTable = staticRegion.slotParamTable.clone();
        this.outputTable = staticRegion.outputTable.clone();
        this.endIns = staticRegion.endIns;
        this.varTypeTable = staticRegion.varTypeTable.clone();
        this.isMethodRegion = staticRegion.isMethodRegion;
        this.spfCaseSet = spfCaseSet;
    }

    //SH: used multiple times by different transformations other than the substitution.
    public DynamicRegion(StaticRegion staticRegion,
                         Stmt dynStmt,
                         SlotTypeTable slotTypeTable,
                         Table.VarTypeTable varTypeTable,
                         SlotParamTable slotParamTable,
                         OutputTable outputTable,
                         boolean isMethodRegion,
                         HashSet<SPFCaseStmt> spfCaseSet) {

        this.dynStmt = dynStmt;
        this.staticRegion = staticRegion;
        this.slotTypeTable = slotTypeTable;
        this.slotParamTable = slotParamTable;
        this.outputTable = outputTable;
        this.endIns = staticRegion.endIns;
        this.varTypeTable = varTypeTable;
        this.isMethodRegion = isMethodRegion;
        this.spfCaseSet = spfCaseSet;
    }
}
