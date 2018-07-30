package gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticEnvironment;

import com.ibm.wala.ssa.*;

import java.util.*;

public class OutputTable extends Table<Integer> {
    public OutputTable(IR ir, boolean isMethodRegion, SlotParamTable slotParamTable, InputTable inputTable) {
        super("Region Output Table", isMethodRegion ? "return" : "slot", "var");
        if (!isMethodRegion)
            computeMethodOutput(ir);
        else
            computeOutputVars(ir, slotParamTable, inputTable);
    }

    //SH: all normal predecessors of an exit node must have a return as the last instruction.
    // if the first return has no use then the method is void.
    private void computeMethodOutput(IR ir) {
        List<SSAReturnInstruction> returnInsList = findAllReturns(ir);
        int resultNum = 0;
        for(SSAReturnInstruction returnIns: returnInsList){
            if(returnIns.getNumberOfUses() == 0){
                return; // a void method, it does not have an output
            }
            else{
            this.add(resultNum, returnIns.getUse(0));
            ++resultNum;
            }
        }
    }

    private List<SSAReturnInstruction> findAllReturns(IR ir) {
        List<SSAReturnInstruction> returnInsList = new ArrayList<>();
        ISSABasicBlock exitBB = ir.getExitBlock();
        List<ISSABasicBlock> retunBBList = (List<ISSABasicBlock>) ir.getControlFlowGraph().getNormalPredecessors(exitBB);
        for(ISSABasicBlock returnBB: retunBBList){
            assert(returnBB.getLastInstruction() instanceof SSAReturnInstruction);
            returnInsList.add((SSAReturnInstruction) returnBB.getLastInstruction());
        }
        return returnInsList;
    }

    private OutputTable() {
        super();
    }

    //SH: outputVars are computed by finding the maximum wala var for each
    //stackSlot and those that are not input or constants.
    private void computeOutputVars(IR ir, SlotParamTable slotParamTable, InputTable inputTable) {
        HashSet<Integer> allSlots = slotParamTable.getSlots();
        Iterator<Integer> slotsIter = allSlots.iterator();
        while (slotsIter.hasNext()) {
            int slot = slotsIter.next();
            Set<Integer> varsForSlot = slotParamTable.getVarsOfSlot(slot);
            Integer slotOutput = Collections.max(varsForSlot);
            if ((inputTable.lookup(slotOutput) == null) && !(ir.getSymbolTable().isConstant(slotOutput)))
                this.add(slot, Collections.max(varsForSlot));
        }
    }

    @Override
    public void print() {
        System.out.println("\nprinting " + tableName + " (" + label1 + "->" + label2 + ")");
        table.forEach((v1, v2) -> System.out.println(v1 + " --------- !w" + v2));
    }

    public OutputTable clone() {
        OutputTable outputTable = new OutputTable();
        outputTable.tableName = this.tableName;
        outputTable.label1 = this.label1;
        outputTable.label2 = this.label2;
        Set<Integer> keys = this.table.keySet();
        Iterator<Integer> iter = keys.iterator();
        while (iter.hasNext()) {
            Integer key = iter.next();
            int value = this.lookup(key);
            outputTable.add(new Integer(key.intValue()), value);
        }
        return outputTable;
    }


    public void makeUniqueKey(int unique) {
        Object[] keys = table.keySet().toArray();
        for (int i = 0; i < keys.length; i++) {
            String varId = Integer.toString(table.get(keys[i]));
            varId = varId.concat(Integer.toString(unique));
            table.put((Integer) keys[i], Integer.valueOf(varId));
        }
    }
}
