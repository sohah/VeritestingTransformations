package gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst;

import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAPhiInstruction;
import com.ibm.wala.ssa.SymbolTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution.Table;

import java.util.*;

//SH: This is the basic table, on which the input and output of the region are defined.
// The table holds the wala vars -> stackSlot mapping if it is not a method region, if it is a method region, then wala vars -> parameters to the method are instead populated in this table.
// In case of a non method region, the map holds for every var all the stackSlots that the var
// can map to, because a var can map to multiple locations. Also non-input an non-output vars mapping for non method regions can appear in this table if we were able to infer their stack slot.


public class SlotParamTable extends Table<int[]> {
    private IR ir;
    private boolean isMethodRegion;


    public SlotParamTable(IR ir, Boolean isMethodRegion) { // var -> param/slot
        super("stack-slot table", "var", isMethodRegion? "param" : "slot");
        this.ir = ir;
        this.isMethodRegion = isMethodRegion;
        if (isMethodRegion)
            populateParam();
        else
            populateSlotsForVars();
    }


    private void populateParam() {
        for(int i = 0; i < ir.getNumberOfParameters(); i++){
            this.add(ir.getParameter(i), new int [i]);
        }

    }

    private SlotParamTable() {
        super();
    }


    private void populateSlotsForVars() {
        StackSlotIVisitor stackSlotIVisitor = new StackSlotIVisitor(ir, this);
        for (SSAInstruction ins : ir.getControlFlowGraph().getInstructions()) {
            if (ins != null)
                ins.visit(stackSlotIVisitor);
        }
        stackSlotPhiPropagation();
    }

    //SH: returns all unique slots in the stackSlotMap. It attempts to do that by flattening out stackSlots of a single
    //var, which can map to multiple locations.
    public HashSet getSlots() {
        HashSet<Integer> allSlots = new HashSet();
        Set<Integer> vars = table.keySet();
        Iterator<Integer> varItr = vars.iterator();
        HashSet<Integer> VarSlotSet = new HashSet();

        while (varItr.hasNext()) {
            Integer var = varItr.next();
            int[] varStackSlots = table.get(var);
            for (int i = 0; i < varStackSlots.length; i++) { //silly, converts an array to HashSet, there should be better ways in Java 8.
                VarSlotSet.add(varStackSlots[i]);
            }
            allSlots.addAll(VarSlotSet);
        }

        return allSlots;
    }

    //SH: returns all vars that have the same stack slot entered in the parameter.
    public Set getVarsOfSlot(int slot) {
        HashSet<Integer> stackSlotVars = new HashSet();
        Set<Integer> vars = table.keySet();
        Iterator<Integer> varIter = vars.iterator();

        while (varIter.hasNext()) {
            HashSet<Integer> varSlotSet = new HashSet();
            Integer var = varIter.next();
            int[] varStackSlots = table.get(var);
            for (int i = 0; i < varStackSlots.length; i++) { //silly, converts an array to HashSet, there should be better ways in Java 8.
                varSlotSet.add(varStackSlots[i]);
            }
            if (varSlotSet.contains(slot))
                stackSlotVars.add(var);
        }
        return stackSlotVars;
    }

    //This tries to infer the stack slots for phi "def" vars and phi "use" vars by either figuring out the stack slots
    // of one "use" var and populate it to be for the phi "def" var, or the opposite,
    // that is the stack slot of the phi "def" was known and so it is propagated to the "use" vars

    private void stackSlotPhiPropagation() {
        boolean changeDetected;
        do {
            changeDetected = false;
            Iterator<? extends SSAInstruction> phiItr = ir.iteratePhis();
            while (phiItr.hasNext()) {
                SSAPhiInstruction phi = (SSAPhiInstruction) phiItr.next();
                int result = phi.getDef();
                int[] phiSlot = lookup(result);
                if (phiSlot == null) { //stack slot of the phi "def" var is unkown
                    int[] slots = getOperandSlot(phi);
                    if (slots != null) {//could figure out the stack slot of a "use"
                        table.put(phi.getDef(), slots);
                        changeDetected = true;
                    }
                } else { //stack slot of the phi "def" var is unkown, propagate it to the "use" vars
                    changeDetected = updatePhiUse(phi, phiSlot);
                }
            }
        } while (changeDetected);
    }

    private boolean updatePhiUse(SSAPhiInstruction phi, int[] slots) {
        boolean changeDetected = false;
        for (int i = 0; i < phi.getNumberOfUses(); i++) {
            if (!isConstant(phi.getUse(i))) {
                int[] useSckSlot = lookup(phi.getUse(i));
                if (useSckSlot == null) {
                    table.put(phi.getUse(i), slots);
                    changeDetected = true;
                }
            }
        }
        return changeDetected;
    }

    private int[] getOperandSlot(SSAPhiInstruction phi) {
        for (int i = 0; i < phi.getNumberOfUses(); i++) {
            int[] useSckSlot = lookup(phi.getUse(i));
            if (useSckSlot != null)
                return useSckSlot;
        }
        return null;
    }

    public boolean isConstant(int operand1) {
        SymbolTable table = ir.getSymbolTable();
        return table.isNumberConstant(operand1) ||
                table.isBooleanOrZeroOneConstant(operand1) ||
                table.isNullConstant(operand1);
    }

    @Override
    public void print() {
        System.out.println("\nRegion Stack Slot Map (var -> " + (isMethodRegion? "param" : "slot") +")");
        table.forEach((var, stackSlots) -> System.out.println("!w" + var + " --------- " + Arrays.toString(stackSlots)));
    }

    public SlotParamTable clone() {
        SlotParamTable newSlotParamTable = new SlotParamTable();
        newSlotParamTable.ir = this.ir;
        newSlotParamTable.tableName = this.tableName;
        newSlotParamTable.label1 = this.label1;
        newSlotParamTable.label2 = this.label2;
        Set<Integer> keys = this.table.keySet();
        Iterator<Integer> iter = keys.iterator();
        while (iter.hasNext()) {
            Integer key = iter.next();
            int[] values = this.lookup(key);
            newSlotParamTable.add(new Integer(key.intValue()), values);
        }
        return newSlotParamTable;
    }
}
