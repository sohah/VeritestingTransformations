package gov.nasa.jpf.symbc.veritesting;

import com.ibm.wala.ssa.*;

import com.ibm.wala.types.TypeReference;
import gov.nasa.jpf.symbc.VeritestingListener;
import gov.nasa.jpf.vm.StackFrame;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;

import java.lang.annotation.ElementType;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;

public class VarUtil {
    String className;
    String methodName;
    IR ir;
    // Maps each WALA IR variable to its corresponding stack slot, if one exists
    HashMap<Integer, Integer> varsMap;

    public HashMap<String, Expression> varCache;

    // these represent the outputs of a veritesting region
    public HashSet<Expression> defLocalVars;

    // contains all the holes in the cnlie AST
    public LinkedHashMap<Expression, Expression> holeHashMap;

    public static int pathCounter=0;
    private static long holeID = 0;

    // contains the return values hole expression found in the region
    public Expression retValVar;

    public static final int getPathCounter() { pathCounter++; return pathCounter; }

    public Expression makeIntermediateVar(int val) {
        String name = "v" + val;
        return makeIntermediateVar(name);
    }

    public Expression makeIntermediateVar(String name) {
        name = className + "." + methodName + "." + name;
        if(varCache.containsKey(name))
            return varCache.get(name);
        HoleExpression holeExpression = new HoleExpression(nextInt(), className, methodName);
        holeExpression.setHole(true, HoleExpression.HoleType.INTERMEDIATE);
        holeExpression.setHoleVarName(name);
        varCache.put(name, holeExpression);
        return holeExpression;
    }

    public Expression makeLocalInputVar(int val) {
        assert(varsMap.containsKey(val));
        String name = className + "." + methodName + ".v" + val;
        if(varCache.containsKey(name))
            return varCache.get(name);
        HoleExpression holeExpression = new HoleExpression(nextInt(), className, methodName);
        holeExpression.setHole(true, HoleExpression.HoleType.LOCAL_INPUT);
        holeExpression.setLocalStackSlot(varsMap.get(val));
        holeExpression.setHoleVarName(name);
        varCache.put(name, holeExpression);
        return holeExpression;
    }

    public Expression makeLocalOutputVar(int val) {
        assert(varsMap.containsKey(val));
        String name = className + "." + methodName + ".v" + val;
        if(varCache.containsKey(name))
            return varCache.get(name);
        HoleExpression holeExpression = new HoleExpression(nextInt(), className, methodName);
        holeExpression.setHole(true, HoleExpression.HoleType.LOCAL_OUTPUT);
        holeExpression.setLocalStackSlot(varsMap.get(val));
        holeExpression.setHoleVarName(name);
        varCache.put(name, holeExpression);
        return holeExpression;
    }

    public VarUtil(IR _ir, String _className, String _methodName) {
        varsMap = new HashMap<> ();
        defLocalVars = new HashSet<>();
        holeHashMap = new LinkedHashMap<>();
        varCache = new HashMap<String, Expression> () {
            @Override
            public Expression put(String key, Expression expression) {
                if(expression instanceof HoleExpression && ((HoleExpression)expression).isHole()) {
                    // using non-hole IntegerConstant object containing 0 as placeholder
                    // for final filled-up hole object
                    if(!holeHashMap.containsKey(expression)) {
                        setLatestWrite(expression);
                        holeHashMap.put(expression, expression);
                        checkReadAfterWrite(expression);
                    }
                    if(((HoleExpression)expression).getHoleType() == HoleExpression.HoleType.FIELD_OUTPUT ||
                            ((HoleExpression)expression).getHoleType() == HoleExpression.HoleType.LOCAL_OUTPUT)
                        defLocalVars.add(expression);
                }
                return super.put(key, expression);
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

        //Propagates mapping from WALA IR variable to local stack slot to all WALA IR variables involved in
        //phi assignment statements
        boolean localVarUpdated;
        do {
            localVarUpdated = false;
            Iterator<? extends SSAInstruction> phiIterator = _ir.iteratePhis();
            while(phiIterator.hasNext()) {
                SSAPhiInstruction phiInstruction = (SSAPhiInstruction) phiIterator.next();
                for(int use = 0; use < phiInstruction.getNumberOfUses(); use++) {
                    int valNum = phiInstruction.getUse(use);
                    if(!isConstant(valNum) && varsMap.containsKey(valNum)) {
                        if(updateLocalVarsForPhi(phiInstruction, valNum)) localVarUpdated = true;
                        break;
                    }
                }
                if(localVarUpdated) break;
                for(int def = 0; def < phiInstruction.getNumberOfDefs(); def++) {
                    int valNum = phiInstruction.getDef(def);
                    if(!isConstant(valNum) && varsMap.containsKey(valNum)) {
                        if(updateLocalVarsForPhi(phiInstruction, valNum)) localVarUpdated = true;
                        break;
                    }
                }
                if(localVarUpdated) break;
            }
        } while(localVarUpdated);
    }

    private void checkReadAfterWrite(Expression expression) {
        HoleExpression holeExpression = ((HoleExpression)expression);
        if(holeExpression.getHoleType() == HoleExpression.HoleType.LOCAL_INPUT) {
            for(HashMap.Entry<Expression, Expression> entry: holeHashMap.entrySet()) {
                HoleExpression holeExpression1 = (HoleExpression) entry.getKey();
                if(holeExpression1.getHoleType() != HoleExpression.HoleType.LOCAL_OUTPUT) continue;
                if(holeExpression.getLocalStackSlot() == holeExpression1.getLocalStackSlot() &&
                        holeExpression1.isLatestWrite)
                    holeExpression.dependsOn = holeExpression1;
            }
        }
        if(holeExpression.getHoleType() == HoleExpression.HoleType.FIELD_INPUT) {
            for(HashMap.Entry<Expression, Expression> entry: holeHashMap.entrySet()) {
                HoleExpression holeExpression1 = (HoleExpression) entry.getKey();
                if(holeExpression1.getHoleType() != HoleExpression.HoleType.FIELD_OUTPUT) continue;
                if(holeExpression.getFieldInfo().equals(holeExpression1.getFieldInfo()) &&
                        holeExpression1.isLatestWrite)
                    holeExpression.dependsOn = holeExpression1;
            }
        }
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

    public Expression addVal(int val) {
        String name = className + "." + methodName + ".v" + val;
        if(varCache.containsKey(name))
            return varCache.get(name);
        Expression ret;
        if(isConstant(val)) {
            ret = new IntConstant(getConstant(val));
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

    public Expression addDefVal(int def) {
        //this assumes that we dont need to do anything special for intermediate vars defined in a region
        if(isLocalVariable(def)) {
            return makeLocalOutputVar(def);
        }
        System.out.println("non-local value cannot be defined (" + def + ")");
        assert(false);
        return null;
    }

    /*private Expression addDefLocalVar(int def) {
        Expression ret = makeLocalOutputVar(def);
        defLocalVars.add(ret);
        return ret;
    }*/

    public Expression addArrayLoadVal(Expression arrayRef, Expression arrayIndex, TypeReference arrayType, HoleExpression.HoleType holeType, SSAArrayLoadInstruction instructionName, String pathLabelString, int pathLabel) {
        assert(holeType == HoleExpression.HoleType.ARRAYLOAD);
        HoleExpression holeExpression = new HoleExpression(nextInt(), className, methodName);
        holeExpression.setHoleVarName(instructionName.toString());
        holeExpression.setHole(true, holeType);
        holeExpression.setArrayInfo(arrayRef, arrayIndex, arrayType, pathLabelString, pathLabel);
        varCache.put(holeExpression.getHoleVarName(), holeExpression);
        holeExpression.toString();
        return holeExpression;
    }

    // def will be value being defined in case of FIELD_INPUT hole
    public Expression addFieldInputVal(int def, int use, String className, String fieldName,
                                       HoleExpression.HoleType holeType, boolean isStaticField) {
        assert(holeType == HoleExpression.HoleType.FIELD_INPUT);
        HoleExpression useHole = null;
        //If the field does not belong to a local object, then it has to be an already created object or a static field
        // meaning use equals -1
        //But the already created object hole takes priority over a local object
        String string = this.className + "." + this.methodName + ".v" + use;
        if(varsMap.containsKey(use) == false) assert(varCache.containsKey(string) || use == -1);
        if(varCache.containsKey(string)) useHole = (HoleExpression) varCache.get(string);
        int localStackSlot = -1;
        if(!isStaticField && (useHole == null)) {
            assert(use != -1);
            localStackSlot = varsMap.get(use);
        }
        HoleExpression holeExpression = new HoleExpression(nextInt(), className, methodName);
        holeExpression.setHole(true, holeType);
        holeExpression.setFieldInfo(className, fieldName, methodName, localStackSlot, -1, null, isStaticField, useHole);
        String name = this.className + "." + this.methodName + ".v" + def;
        holeExpression.setHoleVarName(name);
        if(fieldHasRWOperation(holeExpression, HoleExpression.HoleType.FIELD_OUTPUT, holeHashMap, null, null) &&
                (VeritestingListener.allowFieldReadAfterWrite == false)) {
            VeritestingListener.fieldReadAfterWrite += 1;
            return null;
        }
        varCache.put(holeExpression.getHoleVarName(), holeExpression);
        return holeExpression;
    }

    /*
    Checks if there is a read/write (specified in holeType) operation happening on the same field in holeExpression
    and some hole in holeHashMap.
    This method assumes that holeExpression comes from a method summary, holeHashMap is the hashmap of holes of the
    outer region.
     */
    public static boolean fieldHasRWOperation(HoleExpression holeExpression, HoleExpression.HoleType holeType,
                                        HashMap<Expression, Expression> holeHashMap, InvokeInfo callSiteInfo,
                                              StackFrame stackFrame) {
        assert(holeExpression.getHoleType() == HoleExpression.HoleType.FIELD_INPUT ||
                holeExpression.getHoleType() == HoleExpression.HoleType.FIELD_OUTPUT);
        for(HashMap.Entry<Expression, Expression> entry: holeHashMap.entrySet()) {
            HoleExpression holeExpression1 = (HoleExpression) entry.getKey();
            if(holeExpression1.getHoleType() != holeType) continue;
            //One of the field accesses is non-static, so there cannot be a r/w operation to the same field
            if(holeExpression1.getFieldInfo().isStaticField && !holeExpression.getFieldInfo().isStaticField) continue;
            if(!holeExpression1.getFieldInfo().isStaticField && holeExpression.getFieldInfo().isStaticField) continue;
            if(!holeExpression.getFieldInfo().fieldName.equals(holeExpression1.getFieldInfo().fieldName)) continue;
            //Both field accesses are static and access the same field
            if(holeExpression1.getFieldInfo().isStaticField && holeExpression.getFieldInfo().isStaticField)
                if(holeExpression.getFieldInfo().equals(holeExpression1.getFieldInfo()))
                    return true;
            //At this point, both field accesses operate on the same type of field and are both non-static
            //we now need to determine if these two fields belong to the same object
            //Assume that holeExpression comes from a method summary if callSiteInfo is not null
            if(callSiteInfo == null) return true;
            if(holeExpression.getFieldInfo().localStackSlot == 0) {
                int objRefMS = stackFrame.getLocalVariable(((HoleExpression) callSiteInfo.paramList.get(0)).getLocalStackSlot());
                int objRefOR = stackFrame.getLocalVariable(holeExpression1.getFieldInfo().localStackSlot);
                if(objRefMS == objRefOR) return true;
                else return false;
            } else {
                //We cannot load the object reference for an object that is created locally within the method summary
                return false;
            }
        }
        return false;
    }

    // def will be value being defined in case of FIELD_INPUT hole
    public Expression addFieldOutputVal(Expression writeExpr, int use,
                                       String className,
                                       String fieldName,
                                       HoleExpression.HoleType holeType,
                                        boolean isStaticField) {
        assert(holeType == HoleExpression.HoleType.FIELD_OUTPUT);
        HoleExpression useHole = null;
        //If the field does not belong to a local object, then it has to be an already created object or a static field
        // meaning use equals -1
        //But the already created object hole takes priority over a local object
        String string = this.className + "." + this.methodName + ".v" + use;
        if(varsMap.containsKey(use) == false) assert(varCache.containsKey(string) || use == -1);
        if(varCache.containsKey(string)) useHole = (HoleExpression) varCache.get(string);
        int localStackSlot = -1;
        if(!isStaticField && (useHole == null)) {
            assert(use != -1);
            localStackSlot = varsMap.get(use);
        }
        String name = "FIELD_OUTPUT." + ((HoleExpression)writeExpr).getHoleVarName();
        if(varCache.containsKey(name)) return varCache.get(name);
        HoleExpression holeExpression = new HoleExpression(nextInt(), className, methodName);
        holeExpression.setHole(true, holeType);
        holeExpression.setFieldInfo(className, fieldName, methodName, localStackSlot, -1, writeExpr, isStaticField, useHole);
        holeExpression.setHoleVarName(name);
        if(fieldHasRWOperation(holeExpression, HoleExpression.HoleType.FIELD_INPUT, holeHashMap, null, null) &&
                (VeritestingListener.allowFieldWriteAfterRead == false)) {
            VeritestingListener.fieldWriteAfterRead += 1;
            return null;
        }
        if(fieldHasRWOperation(holeExpression, HoleExpression.HoleType.FIELD_OUTPUT, holeHashMap, null, null) &&
                (VeritestingListener.allowFieldWriteAfterWrite == false)) {
            VeritestingListener.fieldWriteAfterWrite += 1;
            return null;
        }
        varCache.put(name, holeExpression);
        return holeExpression;
    }

    public boolean isConstant(int operand1) {
        SymbolTable table = ir.getSymbolTable();
        return table.isNumberConstant(operand1) ||
                table.isBooleanOrZeroOneConstant(operand1) ||
                table.isNullConstant(operand1);
    }

    public int getConstant(int operand1) {
        assert(isConstant(operand1));
        SymbolTable table = ir.getSymbolTable();
        if(table.isNumberConstant(operand1))
            return table.getIntValue(operand1);
        if(table.isBooleanOrZeroOneConstant(operand1))
            return (table.isTrue(operand1) ? 1 : 0);
        if(table.isNullConstant(operand1))
            return 0;
        System.out.println("Unknown constant type");
        assert(false);
        return -1;
    }

    public void reset() {
        defLocalVars.clear();
        varCache.clear();
        holeHashMap.clear();
        retValVar = null;
    }

    public long nextInt() {
        holeID++;
        return holeID;
    }

    public Expression addInvokeHole(InvokeInfo invokeInfo) {
        HoleExpression holeExpression = new HoleExpression(nextInt(), className, methodName);
        String name = className + "." + methodName + ".v" + invokeInfo.defVal;
        holeExpression.setHole(true, HoleExpression.HoleType.INVOKE);
        holeExpression.setInvokeInfo(invokeInfo);
        //The return value of this invokeVirtual will be this holeExpression object.
        //The only way to fill this hole is to map it to the corresponding method summary return value
        holeExpression.setHoleVarName(name);
        varCache.put(name, holeExpression);
        return holeExpression;
    }

    public void addRetValHole(int use) {
        if(!isConstant(use)) {
            String name = className + "." + methodName + ".v" + use;
            if(!varCache.containsKey(name)) {
                System.out.println("varCache does not contain " + name);
            }
            assert (varCache.containsKey(name));
            retValVar = varCache.get(name);
        } else retValVar = new IntConstant(getConstant(use));
    }

    public void setLatestWrite(Expression expression) {
        HoleExpression holeExpression = (HoleExpression) expression;
        if(holeExpression.getHoleType() == HoleExpression.HoleType.LOCAL_OUTPUT) {
            for(HashMap.Entry<Expression, Expression> entry: holeHashMap.entrySet()) {
                HoleExpression holeExpression1 = (HoleExpression) entry.getKey();
                if(holeExpression1.getHoleType() != HoleExpression.HoleType.LOCAL_OUTPUT) continue;
                if(holeExpression.getLocalStackSlot() == holeExpression1.getLocalStackSlot())
                    holeExpression1.isLatestWrite = false;
            }
        }
        if(holeExpression.getHoleType() == HoleExpression.HoleType.FIELD_OUTPUT) {
            for(HashMap.Entry<Expression, Expression> entry: holeHashMap.entrySet()) {
                HoleExpression holeExpression1 = (HoleExpression) entry.getKey();
                if(holeExpression1.getHoleType() != HoleExpression.HoleType.FIELD_OUTPUT) continue;
                if(holeExpression.getFieldInfo().equals(holeExpression1.getFieldInfo()))
                    holeExpression1.isLatestWrite = false;
            }
        }
    }
}

