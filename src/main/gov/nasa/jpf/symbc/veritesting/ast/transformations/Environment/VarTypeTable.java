package gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment;

import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSAInstruction;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;

import java.util.Iterator;
import java.util.Set;

public class VarTypeTable extends Table<String> {
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

    private VarTypeTable() {
        super();
    }

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

