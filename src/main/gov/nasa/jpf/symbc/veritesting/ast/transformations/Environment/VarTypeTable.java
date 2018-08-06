package gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment;

import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSAInstruction;

import java.util.Iterator;
import java.util.Set;

    public class VarTypeTable extends Table<String> {
        public VarTypeTable(IR ir) {
            super("WalaVarTypeTable", " var ", "type");
            StaticTypeIVisitor staticTypeIVisitor = new StaticTypeIVisitor(ir, this);
            for (SSAInstruction ins : ir.getControlFlowGraph().getInstructions()) {
                if (ins != null)
                    ins.visit(staticTypeIVisitor);
            }
        }

        private VarTypeTable(){
            super();
        }

        public VarTypeTable clone(){
            VarTypeTable varTypeTable = new VarTypeTable();
            varTypeTable.tableName = this.tableName;
            varTypeTable.label1 = this.label1;
            varTypeTable.label2 = this.label2;
            Set<Integer> keys = this.table.keySet();
            Iterator<Integer> iter = keys.iterator();
            while(iter.hasNext()){
                Integer key = iter.next();
                String type = this.lookup(key);
                varTypeTable.add(new Integer(key.intValue()),type);
            }
            return varTypeTable;
        }
    }

