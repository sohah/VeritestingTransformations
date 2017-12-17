package gov.nasa.jpf.symbc.veritesting;

import com.ibm.wala.ssa.*;
import gov.nasa.jpf.symbc.numeric.*;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;

public class VarUtil {
    String className;
    String methodName;
    IR ir;
    // Maps each WALA IR variable to its corresponding stack slot, if one exists
    HashMap<Integer, Integer> varsMap;

    public HashMap<String, IntegerExpression> varCache;

    // these represent the outputs of a veritesting region
    public HashSet<IntegerExpression> defLocalVars;

    // contains all the holes in the cnlie AST
    public HashMap<IntegerExpression, IntegerExpression> holeHashMap;

    public static int pathCounter=0;
    private static long holeID = 0;


    public static final int getPathCounter() { pathCounter++; return pathCounter; }

    public SymbolicInteger makeIntermediateVar(int val) {
        String name = "v" + val;
        return makeIntermediateVar(name);
    }

    public SymbolicInteger makeIntermediateVar(String name) {
        if(varCache.containsKey(name))
            return (SymbolicInteger) varCache.get(name);
        SymbolicInteger s = new SymbolicInteger(name, MinMax.getVarMinInt(name), MinMax.getVarMaxInt(name));
        s.setHole(false, Expression.HoleType.NONE);
        varCache.put(name, s);
        return s;
    }

    public IntegerExpression makeLocalInputVar(int val) {
        assert(varsMap.containsKey(val));
        if(varCache.containsKey("v" + val))
            return varCache.get("v" + val);
        IntegerExpression integerExpression = new IntegerConstant(nextInt());
        integerExpression.setHole(true, Expression.HoleType.LOCAL_INPUT);
        integerExpression.setLocalStackSlot(varsMap.get(val));
        varCache.put("v" + val, integerExpression);
        return integerExpression;
    }

    public IntegerExpression makeLocalOutputVar(int val) {
        assert(varsMap.containsKey(val));
        if(varCache.containsKey("v" + val))
            return varCache.get("v" + val);
        IntegerExpression integerExpression = new IntegerConstant(nextInt());
        integerExpression.setHole(true, Expression.HoleType.LOCAL_OUTPUT);
        integerExpression.setLocalStackSlot(varsMap.get(val));
        integerExpression.setHoleVarName("v" + val);
        varCache.put("v" + val, integerExpression);
        return integerExpression;
    }

    public VarUtil(IR _ir, String _className, String _methodName) {
        varsMap = new HashMap<> ();
        defLocalVars = new HashSet<>();
        holeHashMap = new HashMap<>();
        varCache = new HashMap<String, IntegerExpression> () {
            @Override
            public IntegerExpression put(String key, IntegerExpression integerExpression) {
                if(integerExpression instanceof IntegerConstant && integerExpression.isHole()) {
                    // using non-hole IntegerConstant object containing 0 as placeholder
                    // for final filled-up hole object
                    holeHashMap.put(integerExpression, integerExpression);
                }
                return super.put(key, integerExpression);
            }
        };
        className = _className;
        methodName = _methodName;
        ir = _ir;
        // Report local stack slot information (if it exists) for every WALA IR variable
        _ir.visitNormalInstructions(new SSAInstruction.Visitor() {
            void getStackSlots(SSAInstruction ssaInstruction) {
                for (int v = 0; v < ssaInstruction.getNumberOfUses(); v++) {
                    int valNum = ssaInstruction.getUse(v);
                    int[] localNumbers = _ir.findLocalsForValueNumber(ssaInstruction.iindex, valNum);
                    if (localNumbers != null) {
                        for (int k = 0; k < localNumbers.length; k++) {
                            /*System.out.println("at pc(" + ssaInstruction +
                                    "), valNum(" + valNum + ") is local var(" + localNumbers[k] + ", " +
                                    _ir.getSymbolTable().isConstant(valNum) + ") uses");*/
                            if(!_ir.getSymbolTable().isConstant(valNum))
                                varsMap.put(valNum, localNumbers[k]);
                        }
                    }
                }
                for (int def = 0; def < ssaInstruction.getNumberOfDefs(); def++) {
                    int valNum = ssaInstruction.getDef(def);
                    int[] localNumbers = _ir.findLocalsForValueNumber(ssaInstruction.iindex, valNum);
                    if (localNumbers != null) {
                        for (int k = 0; k < localNumbers.length; k++) {
                            /*System.out.println("at pc(" + ssaInstruction +
                                    "), valNum(" + valNum + ") is local var(" + localNumbers[k] + ", " +
                                    _ir.getSymbolTable().isConstant(valNum) + ") defs");*/
                            if(!_ir.getSymbolTable().isConstant(valNum)) {
                                varsMap.put(valNum, localNumbers[k]);
                                // Assume var defined by phi instruction must be the same local variable as all its uses

                            }
                        }
                    } else if(ssaInstruction instanceof SSAPhiInstruction){
                        // Assume var defined by phi instruction must be the same local variable as one of its uses
                        for(int use = 0; use < ssaInstruction.getNumberOfUses(); use++) {
                            if(isLocalVariable(use)) {
                                if(varsMap.containsKey(def)) {
                                    System.out.println("Multiple local variables merged in SSAPhiInstruction at offset "
                                            + ssaInstruction.iindex);
                                    assert(false);
                                } else {
                                    varsMap.put(def, varsMap.get(use));
                                }
                            }
                        }
                    }
                }
            }
            @Override
            public void visitGoto(SSAGotoInstruction instruction) {
                getStackSlots(instruction);
                super.visitGoto(instruction);
            }

            @Override
            public void visitArrayLoad(SSAArrayLoadInstruction instruction) {
                getStackSlots(instruction);
                super.visitArrayLoad(instruction);
            }

            @Override
            public void visitArrayStore(SSAArrayStoreInstruction instruction) {
                getStackSlots(instruction);
                super.visitArrayStore(instruction);
            }

            @Override
            public void visitBinaryOp(SSABinaryOpInstruction instruction) {
                getStackSlots(instruction);
                super.visitBinaryOp(instruction);
            }

            @Override
            public void visitUnaryOp(SSAUnaryOpInstruction instruction) {
                getStackSlots(instruction);
                super.visitUnaryOp(instruction);
            }

            @Override
            public void visitConversion(SSAConversionInstruction instruction) {
                getStackSlots(instruction);
                super.visitConversion(instruction);
            }

            @Override
            public void visitComparison(SSAComparisonInstruction instruction) {
                getStackSlots(instruction);
                super.visitComparison(instruction);
            }

            @Override
            public void visitConditionalBranch(SSAConditionalBranchInstruction instruction) {
                getStackSlots(instruction);
                super.visitConditionalBranch(instruction);
            }

            @Override
            public void visitSwitch(SSASwitchInstruction instruction) {
                getStackSlots(instruction);
                super.visitSwitch(instruction);
            }

            @Override
            public void visitReturn(SSAReturnInstruction instruction) {
                getStackSlots(instruction);
                super.visitReturn(instruction);
            }

            @Override
            public void visitGet(SSAGetInstruction instruction) {
                getStackSlots(instruction);
                super.visitGet(instruction);
            }

            @Override
            public void visitPut(SSAPutInstruction instruction) {
                getStackSlots(instruction);
                super.visitPut(instruction);
            }

            @Override
            public void visitInvoke(SSAInvokeInstruction instruction) {
                getStackSlots(instruction);
                super.visitInvoke(instruction);
            }

            @Override
            public void visitNew(SSANewInstruction instruction) {
                getStackSlots(instruction);
                super.visitNew(instruction);
            }

            @Override
            public void visitArrayLength(SSAArrayLengthInstruction instruction) {
                getStackSlots(instruction);
                super.visitArrayLength(instruction);
            }

            @Override
            public void visitThrow(SSAThrowInstruction instruction) {
                getStackSlots(instruction);
                super.visitThrow(instruction);
            }

            @Override
            public void visitMonitor(SSAMonitorInstruction instruction) {
                getStackSlots(instruction);
                super.visitMonitor(instruction);
            }

            @Override
            public void visitCheckCast(SSACheckCastInstruction instruction) {
                getStackSlots(instruction);
                super.visitCheckCast(instruction);
            }

            @Override
            public void visitInstanceof(SSAInstanceofInstruction instruction) {
                getStackSlots(instruction);
                super.visitInstanceof(instruction);
            }

            @Override
            public void visitPhi(SSAPhiInstruction instruction) {
                getStackSlots(instruction);
                super.visitPhi(instruction);
            }

            @Override
            public void visitPi(SSAPiInstruction instruction) {
                getStackSlots(instruction);
                super.visitPi(instruction);
            }

            @Override
            public void visitGetCaughtException(SSAGetCaughtExceptionInstruction instruction) {
                getStackSlots(instruction);
                super.visitGetCaughtException(instruction);
            }

            @Override
            public void visitLoadMetadata(SSALoadMetadataInstruction instruction) {
                getStackSlots(instruction);
                super.visitLoadMetadata(instruction);
            }
        });

        boolean localVarUpdated;
        do {
            localVarUpdated = false;
            Iterator<? extends SSAInstruction> phiIterator = _ir.iteratePhis();
            while(phiIterator.hasNext()) {
                SSAPhiInstruction phiInstruction = (SSAPhiInstruction) phiIterator.next();
                for(int use = 0; use < phiInstruction.getNumberOfUses(); use++) {
                    int valNum = phiInstruction.getUse(use);
                    if(!isConstant(valNum) && varsMap.containsKey(valNum)) {
                        localVarUpdated = updateLocalVarsForPhi(phiInstruction, valNum);
                        break;
                    }
                }
                if(localVarUpdated) continue;
                for(int def = 0; def < phiInstruction.getNumberOfDefs(); def++) {
                    int valNum = phiInstruction.getDef(def);
                    if(!isConstant(valNum) && varsMap.containsKey(valNum)) {
                        localVarUpdated = updateLocalVarsForPhi(phiInstruction, valNum);
                        break;
                    }
                }
            }
        } while(localVarUpdated);
    }

    private boolean updateLocalVarsForPhi(SSAPhiInstruction phiInstruction, int val) {
        boolean ret = false;
        for(int use = 0; use < phiInstruction.getNumberOfUses(); use++) {
            int useValNum = phiInstruction.getUse(use);
            if(useValNum == val || isConstant(useValNum)) continue;
            if(varsMap.containsKey(useValNum)) continue;
            else {
                varsMap.put(useValNum, varsMap.get(val));
                ret = true;
            }
        }
        for(int def = 0; def < phiInstruction.getNumberOfDefs(); def++) {
            int defValNum = phiInstruction.getDef(def);
            if(defValNum == val || isConstant(defValNum)) continue;
            if(varsMap.containsKey(defValNum)) continue;
            else {
                varsMap.put(defValNum, varsMap.get(val));
                ret = true;
            }
        }
        return ret;
    }

    public IntegerExpression addVal(int val) {
        String name = "v" + val;
        if(varCache.containsKey(name))
            return varCache.get(name);
        IntegerExpression ret;
        if(ir.getSymbolTable().isConstant(val)) {
            ret = new IntegerConstant(getConstant(val));
            varCache.put(name, ret);
            return ret;
        }
        if(isLocalVariable(val)) ret = makeLocalInputVar(val);
        else ret = makeIntermediateVar(val);
        varCache.put(name, ret);
        return ret;
    }

    public boolean isLocalVariable(int val) {
        return varsMap.containsKey(val);
    }

    public int getLocalVarSlot(int val) {
        if(isLocalVariable(val)) return varsMap.get(val);
        else return -1;
    }

    public IntegerExpression addDefVal(int def) {
        //this assumes that we dont need to do anything special for intermediate vars defined in a region
        if(isLocalVariable(def)) {
            return addDefLocalVar(def);
        }
        System.out.println("non-local value cannot be defined");
        assert(false);
        return null;
    }

    private IntegerExpression addDefLocalVar(int def) {
        IntegerExpression ret = makeLocalOutputVar(def);
        defLocalVars.add(ret);
        return ret;
    }

    public boolean isConstant(int operand1) {
        return ir.getSymbolTable().isConstant(operand1);
    }

    public int getConstant(int operand1) {
        assert(isConstant(operand1));
        return ir.getSymbolTable().getIntValue(operand1);
    }

    public void reset() {
        defLocalVars.clear();
        varCache.clear();
        holeHashMap.clear();
    }

    public long nextInt() {
        holeID++;
        return holeID;
    }
}

