package gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment;

import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSAInstruction;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;

import java.util.Iterator;
import java.util.Set;

/**
 * An environment table that holds all vars to types.
 */
public class VarTypeTable extends Table<String> {
    /**
     * Constructor that is used to generate the type table for a method region.
     * @param ir
     */
    public VarTypeTable(IR ir) {
        super("WalaVarTypeTable", " var ", "type");
        StaticTypeIVisitor staticTypeIVisitor = new StaticTypeIVisitor(ir, this, new Pair(-100, -100));

        for (SSAInstruction ins : ir.getControlFlowGraph().getInstructions()) {
            if (ins != null)
                ins.visit(staticTypeIVisitor);
        }

        Iterator<? extends SSAInstruction> phiItr = ir.iteratePhis();
        while (phiItr.hasNext()) {
            SSAInstruction ins = phiItr.next();
            if (ins != null)
                ins.visit(staticTypeIVisitor);
        }
    }

    /**
     * Constructor that is used to generate the type table for a conditional region, by specifying the boundaries of variables inside the region.
     * @param ir Wala IR that corresponds to the method that the region is discovered from.
     * @param firstUseLastDef A pair of the first Use Var and the Last Def Var numbers inside the region.
     */
    public VarTypeTable(IR ir, Pair<Integer, Integer> firstUseLastDef) {
        super("WalaVarTypeTable", " var ", "type");
        StaticTypeIVisitor staticTypeIVisitor = new StaticTypeIVisitor(ir, this, firstUseLastDef);
        for (SSAInstruction ins : ir.getControlFlowGraph().getInstructions()) {
            if (ins != null)
                ins.visit(staticTypeIVisitor);
        }
        Iterator<? extends SSAInstruction> phiItr = ir.iteratePhis();
        while (phiItr.hasNext()) {
            phiItr.next().visit(staticTypeIVisitor);
        }
    }

    /**
     * Default constructor.
     */
    private VarTypeTable() {
        super();
    }

    /**
     * Clones the VarTypeTable to a new VarTypeTable, by creating new enteries for the keys.
     * @return A new VarTypeTable that has a new copy for the keys.
     */
    public VarTypeTable clone() {
        VarTypeTable varTypeTable = new VarTypeTable();
        varTypeTable.tableName = this.tableName;
        varTypeTable.label1 = this.label1;
        varTypeTable.label2 = this.label2;
        Set<Integer> keys = this.table.keySet();
        Iterator<Integer> iter = keys.iterator();
        while (iter.hasNext()) {
            Integer key = iter.next();
            String type = this.lookup(key);
            varTypeTable.add(new Integer(key.intValue()), type);
        }
        return varTypeTable;
    }
}

