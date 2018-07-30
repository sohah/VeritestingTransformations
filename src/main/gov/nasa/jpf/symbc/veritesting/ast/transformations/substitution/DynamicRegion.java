package gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution;

import gov.nasa.jpf.symbc.veritesting.ast.def.Region;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.OutputTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StackSlotTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.typepropagation.WalaNumTypesTable;

public class DynamicRegion implements Region {

    public static int uniqueCounter = 0;
    public final Stmt dynStmt;
    public final SlotTypeTable slotTypeTable;
    public final ValueSymbolTable valueSymbolTable;
    public final StackSlotTable stackSlotTable;
    public final OutputTable outputTable;
    public final StaticRegion staticRegion;
    public final WalaNumTypesTable walaNumTypesTable;
    public final int endIns;


    public DynamicRegion(StaticRegion staticRegion, Stmt dynStmt, SlotTypeTable slotTypeTable, ValueSymbolTable valueSymbolTable) {

        this.staticRegion = staticRegion;
        this.dynStmt = dynStmt;
        this.valueSymbolTable = valueSymbolTable;
        this.slotTypeTable = slotTypeTable;
        this.stackSlotTable = staticRegion.stackSlotTable.clone();
        this.outputTable = staticRegion.outputTable.clone();
        this.endIns = staticRegion.endIns;
        this.walaNumTypesTable = new WalaNumTypesTable();
    }

    public DynamicRegion(StaticRegion staticRegion, Stmt dynStmt, SlotTypeTable slotTypeTable, ValueSymbolTable valueSymbolTable, StackSlotTable stackSlotTable, OutputTable outputTable) {
        this.dynStmt = dynStmt;
        this.staticRegion = staticRegion;
        this.slotTypeTable = slotTypeTable;
        this.valueSymbolTable = valueSymbolTable;
        this.stackSlotTable = stackSlotTable;
        this.outputTable = outputTable;
        this.endIns = staticRegion.endIns;
        this.walaNumTypesTable = new WalaNumTypesTable();
    }

    public DynamicRegion(StaticRegion staticRegion, Stmt dynStmt, SlotTypeTable slotTypeTable, ValueSymbolTable valueSymbolTable, WalaNumTypesTable walaNumTypesTable) {
        this.staticRegion = staticRegion;
        this.dynStmt = dynStmt;
        this.valueSymbolTable = valueSymbolTable;
        this.slotTypeTable = slotTypeTable;
        this.stackSlotTable = staticRegion.stackSlotTable.clone();
        this.outputTable = staticRegion.outputTable.clone();
        this.endIns = staticRegion.endIns;
        this.walaNumTypesTable = walaNumTypesTable;
    }
}
