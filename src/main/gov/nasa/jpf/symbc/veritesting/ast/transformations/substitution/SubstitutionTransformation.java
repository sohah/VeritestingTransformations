package gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution;

import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAPhiInstruction;
import com.ibm.wala.ssa.SymbolTable;
import gov.nasa.jpf.symbc.veritesting.ast.def.Region;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.DefaultTransformation;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.linearization.LinearizationVisitor;
import za.ac.sun.cs.green.expr.Expression;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;

public class SubstitutionTransformation extends DefaultTransformation {
    private IR ir;
    public HashMap<Integer, int[]> stackSlotMap;
    public HashMap<Expression, Integer> valueMap;


    @Override
    public Region execute(Region region) {
        ir = region.ir;
        populateWalaVars();
        return new Region(region.stmt, region.ir, stackSlotMap, valueMap);
    }

    private void populateWalaVars() {
        StackSlotIVisitor stackSlotIVisitor = new StackSlotIVisitor(ir);
        for (SSAInstruction ins :ir.getControlFlowGraph().getInstructions()) {
            if(ins != null)
                ins.visit(stackSlotIVisitor);
        }
        stackSlotMap = stackSlotIVisitor.stackSlotMap;
        stackSlotPhiPropagation();
    }

    private void stackSlotPhiPropagation(){
        boolean localVarUpdated;
        do {
            localVarUpdated = false;
            Iterator<? extends SSAInstruction> phiIterator = ir.iteratePhis();
            while(phiIterator.hasNext()) {
                SSAPhiInstruction phiInstruction = (SSAPhiInstruction) phiIterator.next();
                for(int use = 0; use < phiInstruction.getNumberOfUses(); use++) {
                    int valNum = phiInstruction.getUse(use);
                    if(!isConstant(valNum) && stackSlotMap.containsKey(valNum)) {
                        if(updateLocalVarsForPhi(phiInstruction, valNum)) localVarUpdated = true;
                        break;
                    }
                }
                if(localVarUpdated) break;
                for(int def = 0; def < phiInstruction.getNumberOfDefs(); def++) {
                    int valNum = phiInstruction.getDef(def);
                    if(!isConstant(valNum) && stackSlotMap.containsKey(valNum)) {
                        if(updateLocalVarsForPhi(phiInstruction, valNum)) localVarUpdated = true;
                        break;
                    }
                }
                if(localVarUpdated) break;
            }
        } while(localVarUpdated);
    }


    private boolean isConstant(int operand1) {
        SymbolTable table = ir.getSymbolTable();
        return table.isNumberConstant(operand1) ||
                table.isBooleanOrZeroOneConstant(operand1) ||
                table.isNullConstant(operand1);
    }

    private boolean updateLocalVarsForPhi(SSAPhiInstruction phiInstruction, int val) {
        boolean ret = false;
        for(int use = 0; use < phiInstruction.getNumberOfUses(); use++) {
            int useValNum = phiInstruction.getUse(use);
            if(useValNum == val || isConstant(useValNum)) continue;
            if (!stackSlotMap.containsKey(useValNum)) {
                stackSlotMap.put(useValNum, stackSlotMap.get(val));
                ret = true;
            }
        }
        for(int def = 0; def < phiInstruction.getNumberOfDefs(); def++) {
            int defValNum = phiInstruction.getDef(def);
            if(defValNum == val || isConstant(defValNum)) continue;
            if (!stackSlotMap.containsKey(defValNum)) {
                stackSlotMap.put(defValNum, stackSlotMap.get(val));
                ret = true;
            }
        }
        return ret;
    }

    private void printStackSlotMap(){
        System.out.println("now printing Stack Slot Map");
        stackSlotMap.forEach((var, stackSlots) -> System.out.println(var + " --------- " + Arrays.toString(stackSlots)));
        System.out.println("end of Stack Slot Map");
    }

}

