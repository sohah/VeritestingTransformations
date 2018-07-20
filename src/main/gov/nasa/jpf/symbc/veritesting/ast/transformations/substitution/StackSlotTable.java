package gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution;

import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAPhiInstruction;
import com.ibm.wala.ssa.SymbolTable;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;

public class StackSlotTable {

    private HashMap<Integer, int[]> stackSlotMap;
    public IR ir;

    public StackSlotTable(IR ir) {
        this.ir = ir;
        populateWalaVars();
    }

    private void populateWalaVars() {
        StackSlotIVisitor stackSlotIVisitor = new StackSlotIVisitor(ir);
        for (SSAInstruction ins : ir.getControlFlowGraph().getInstructions()) {
            if (ins != null)
                ins.visit(stackSlotIVisitor);
        }
        stackSlotMap = stackSlotIVisitor.stackSlotMap;
        stackSlotPhiPropagation();
    }

    public int[] lookup(Integer var) {
        if (var != null)
            return stackSlotMap.get(var);
        else
            try {
                throw new StaticRegionException("Cannot lookup the stack slot for a null var.");
            } catch (StaticRegionException e) {
                System.out.println(e.getMessage());
            }
        return null;
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
                        stackSlotMap.put(phi.getDef(), slots);
                        changeDetected = true;
                    }
                } else { ////stack slot of the phi "def" var is unkown, propagate it to the "use" vars
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
                    stackSlotMap.put(phi.getUse(i), slots);
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

    public void printStackSlotMap() {
        System.out.println("\nprinting Stack Slot Map");
        stackSlotMap.forEach((var, stackSlots) -> System.out.println(var + " --------- " + Arrays.toString(stackSlots)));
    }
}
