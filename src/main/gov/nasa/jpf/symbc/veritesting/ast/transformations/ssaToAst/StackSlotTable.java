package gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst;

import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAPhiInstruction;
import com.ibm.wala.ssa.SymbolTable;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StackSlotIVisitor;

import java.util.*;

//SH: This holds the wala vars to stackSlot mapping. The map holds for every var all the stackSlots that the var
// can map to, because a var can map to multiple locations.


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

    //SH: returns all unique slots in the stackSlotMap. It attempts to do that by flattening out stackSlots of a single
    //var, which can map to multiple locations.
    public HashSet getSlots(){
        HashSet<Integer> allSlots = new HashSet();
        Set<Integer> vars = stackSlotMap.keySet();
        Iterator<Integer> varItr = vars.iterator();
        HashSet<Integer> VarSlotSet = new HashSet();

        while (varItr.hasNext()){
            Integer var = varItr.next();
            int[] varStackSlots = stackSlotMap.get(var);
            for(int i=0; i<varStackSlots.length; i++){ //silly, converts an array to HashSet, there should be better ways in Java 8.
                VarSlotSet.add(varStackSlots[i]);
            }
            allSlots.addAll(VarSlotSet);
        }

        return allSlots;
    }

    //SH: returns all vars that have the same stack slot entered in the parameter.
    public HashSet getVarsOfSlot(int slot){
        HashSet<Integer> stackSlotVars = new HashSet();
        HashSet<Integer> vars = (HashSet<Integer>) stackSlotMap.keySet();
        Iterator<Integer> varIter = vars.iterator();
        HashSet<Integer> varSlotSet = new HashSet();

        while (varIter.hasNext()) {
            Integer var = varIter.next();
            int[] varStackSlots = stackSlotMap.get(var);
            for (int i = 0; i < varStackSlots.length; i++) { //silly, converts an array to HashSet, there should be better ways in Java 8.
                varSlotSet.add(varStackSlots[i]);
            }
            if(varSlotSet.contains(slot))
                stackSlotVars.add(var);
        }
        return vars;
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
        System.out.println("\nRegion Stack Slot Map");
        stackSlotMap.forEach((var, stackSlots) -> System.out.println(var + " --------- " + Arrays.toString(stackSlots)));
    }
}
