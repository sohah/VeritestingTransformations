package gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment;

import com.ibm.wala.ssa.IR;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.ExprRegionInputVisitor;

//SH: this class populates the input variables for the region. it does so by computing the first var use for slots.

public class InputTable extends Table<Integer> {
    public final IR ir;

    public InputTable(IR ir, boolean isMethodRegion, SlotParamTable slotParamTable, Stmt stmt) {
        super("Region Input Table", "var", isMethodRegion ? "param" : "slot");
        this.ir = ir;
        if (isMethodRegion) // all parameters are input
            computeMethodInputVars(slotParamTable);
        else {//only first instances of vars to slots execluding defs.
            computeRegionInput(slotParamTable, stmt);
        }
    }

    private void computeMethodInputVars(SlotParamTable slotParamTable) {
        for (Integer var : slotParamTable.getKeys()) {
            this.add(var, slotParamTable.lookup(var)[0]);
        }
    }

    private void computeRegionInput(SlotParamTable slotParamTable, Stmt stmt) {
        ExprRegionInputVisitor exprRegionInputVisitor = new ExprRegionInputVisitor(this, slotParamTable);
        RegionInputVisitor regionInputVisitor = new RegionInputVisitor(exprRegionInputVisitor);
        stmt.accept(regionInputVisitor);
    }

    @Override
    public void print() {
        System.out.println("\nprinting " + tableName + " (" + label1 + "->" + label2 + ")");
        table.forEach((v1, v2) -> System.out.println("!w" + v1 + " --------- " + v2));
    }
}
