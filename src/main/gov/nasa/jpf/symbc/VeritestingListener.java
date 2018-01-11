/*
 * Copyright (C) 2014, United States Government, as represented by the
 * Administrator of the National Aeronautics and Space Administration.
 * All rights reserved.
 *
 * Symbolic Pathfinder (jpf-symbc) is licensed under the Apache License, 
 * Version 2.0 (the "License"); you may not use this file except
 * in compliance with the License. You may obtain a copy of the License at
 * 
 *        http://www.apache.org/licenses/LICENSE-2.0. 
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and 
 * limitations under the License.
 */


package gov.nasa.jpf.symbc;


import gov.nasa.jpf.Config;
import gov.nasa.jpf.JPF;
import gov.nasa.jpf.PropertyListenerAdapter;
import gov.nasa.jpf.jvm.bytecode.GOTO;
import gov.nasa.jpf.symbc.numeric.*;
import gov.nasa.jpf.symbc.numeric.solvers.SolverTranslator;
import gov.nasa.jpf.symbc.veritesting.*;
import gov.nasa.jpf.vm.*;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.Operation;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;

public class VeritestingListener extends PropertyListenerAdapter  {

  public static HashMap<String, VeritestingRegion> veritestingRegions;

  public VeritestingListener(Config conf, JPF jpf) {
  }
 
  // helper function to print local vars
  private void printLocals(MethodInfo mi, StackFrame mysf) {
    // StackFrame mysf = sf.getPrevious();
    LocalVarInfo[] lvi = mysf.getLocalVars();
          
    String lvs = "";
    for (LocalVarInfo lv: lvi){
      lvs = lvs +  lv.getType() + " " + lv.getName() + ", ";
    }
    System.out.printf("vars: %s\n", lvs);

    for (int i = 0; i < lvi.length; ++i) {
      Expression exp = (Expression)mysf.getLocalAttr(i);
      if (exp != null){
        System.out.printf("SYM: %s = %s\n", lvi[i].getName(), exp.toString());
      }
      else{
        int slot = lvi[i].getSlotIndex();
        System.out.printf("CON: %s = %s\n", lvi[i].getName(), mysf.getSlot(slot));
      }
    }
  }

  // adapted from bytecodes/IFEQ.java
  public PathCondition getPC(VM vm, ThreadInfo ti, Instruction instructionToExecute, PathCondition pc) {
    ChoiceGenerator <?> cg;
    // if (!ti.isFirstStepInsn()) { // first time around
    //   cg = new PCChoiceGenerator(1);
    //   ((PCChoiceGenerator)cg).setOffset(instructionToExecute.getPosition());
    //   ((PCChoiceGenerator)cg).setMethodName(ti.getTopFrame().getMethodInfo().getFullName());
    //   vm.getSystemState().setNextChoiceGenerator(cg);
    //   return null;
    // } else {  // this is what really returns results
      cg = vm.getSystemState().getChoiceGenerator();
      assert (cg instanceof PCChoiceGenerator) : "expected PCChoiceGenerator, got: " + cg;
    // }
    ChoiceGenerator<?> prev_cg = cg.getPreviousChoiceGeneratorOfType(PCChoiceGenerator.class);
    if (prev_cg == null) {
      pc = new PathCondition();
      System.out.println("creating new PathCondition");
    }
    else {
      pc = ((PCChoiceGenerator)prev_cg).getCurrentPC();
      System.out.println("got PathCondition from prev_cg");
    }
    assert pc != null;
    return pc;
  }

  public SymbolicInteger makeSymbolicInteger(String name) {
    //return new SymbolicInteger(name, MinMax.getVarMinInt(name), MinMax.getVarMaxInt(name));
    return new SymbolicInteger(name, Integer.MIN_VALUE, Integer.MAX_VALUE);
  }

  public static int pathLabelCount = 1;

  public void executeInstruction(VM vm, ThreadInfo ti, Instruction instructionToExecute) {
    Config conf = ti.getVM().getConfig();
    String[] lazy = conf.getStringArray("listener");
    if (lazy == null || !lazy[0].contains("Veritesting"))
      return;
    if(veritestingRegions == null) {
      String classPath = conf.getStringArray("classpath")[0] + "/";
      String className = conf.getString("target");
      // should be like VeritestingPerf.testMe4([II)V aka jvm internal format
      VeritestingMain veritestingMain = new VeritestingMain(className + ".class");
      long startTime = System.nanoTime();
      veritestingMain.analyzeForVeritesting(classPath, className);
      long endTime = System.nanoTime();
      long duration = (endTime - startTime) / 1000000; //milliseconds
      System.out.println("veritesting analysis took " + duration + " milliseconds");
      System.out.println("Number of veritesting regions = " + veritestingRegions.size());
    }
    String key = ti.getTopFrame().getClassInfo().getName() + "." + ti.getTopFrame().getMethodInfo().getName() +
            "#" + ti.getTopFrame().getPC().getPosition();
    if(veritestingRegions != null && veritestingRegions.containsKey(key)) {
      VeritestingRegion region = veritestingRegions.get(key);
      StackFrame sf = ti.getTopFrame();
      InstructionInfo instructionInfo = new InstructionInfo(ti).invoke();
      if(instructionInfo == null) return;
      Operation.Operator trueComparator = instructionInfo.getTrueComparator();
      Operation.Operator falseComparator = instructionInfo.getFalseComparator();
      int numOperands = instructionInfo.getNumOperands();
      PathCondition pc;
      pc = ((PCChoiceGenerator) ti.getVM().getSystemState().getChoiceGenerator()).getCurrentPC();
      PathCondition eqPC = pc.make_copy();
      PathCondition nePC = pc.make_copy();
      IntegerExpression sym_v = (IntegerExpression) sf.getOperandAttr();
      eqPC._addDet(GreenToSPFComparator(trueComparator), sym_v, 0);
      nePC._addDet(GreenToSPFComparator(falseComparator), sym_v, 0);
      boolean eqSat = eqPC.simplify();
      boolean neSat = nePC.simplify();
      if (!eqSat && !neSat) {
        System.out.println("both sides of branch at offset " + ti.getTopFrame().getPC().getPosition() + " are unsat");
        assert (false);
      }
      if ((eqSat && !neSat) || (!eqSat && neSat)) {
        return;
      }
      FillHolesOutput fillHolesOutput =
              fillHoles(region.getHoleHashMap(), instructionInfo, sf, ti);
      if(fillHolesOutput.holeHashMap == null) return;
      Expression summaryExpression = region.getSummaryExpression();
      Expression finalSummaryExpression = summaryExpression;
      if(fillHolesOutput.additionalAST != null)
        finalSummaryExpression = new Operation(Operation.Operator.AND, summaryExpression, fillHolesOutput.additionalAST);
      finalSummaryExpression = fillASTHoles(finalSummaryExpression, fillHolesOutput.holeHashMap); //not constant-folding for now
      //pc._addDet(new ComplexNonLinearIntegerConstraint((ComplexNonLinearIntegerExpression)constantFold(summaryExpression)));
      pc._addDet(new GreenConstraint(finalSummaryExpression));
      if(!pc.simplify()) {
        System.out.println("veritesting region added unsat summary");
        assert(false);
      }
      if (!populateOutputs(region.getOutputVars(), fillHolesOutput.holeHashMap, sf, ti)) {
        return;
      }

      Instruction insn = instructionToExecute;
      while (insn.getPosition() != region.getEndInsnPosition()) {
        if (insn instanceof GOTO && (((GOTO) insn).getTarget().getPosition() <= region.getEndInsnPosition()))
          insn = ((GOTO) insn).getTarget();
        else insn = insn.getNext();
      }
      while (numOperands > 0) {
        sf.pop();
        numOperands--;
      }
      ((PCChoiceGenerator) ti.getVM().getSystemState().getChoiceGenerator()).setCurrentPC(pc);
      ti.setNextPC(insn);
      pathLabelCount += 1;
    }
  }

  private Comparator GreenToSPFComparator(Operation.Operator operator) {
    switch(operator) {
      case EQ: return Comparator.EQ;
      case NE: return Comparator.NE;
      case LT: return Comparator.LT;
      case LE: return Comparator.LE;
      case GT: return Comparator.GT;
      case GE: return Comparator.GE;
      case AND: return Comparator.LOGICAL_AND;
      case OR: return Comparator.LOGICAL_OR;
      default:
        System.out.println("Cannot convert Green operator (" + operator + ") to SPF comparator" );
        assert(false);
        break;
    }
    return null;
  }

  /*
  write all outputs of the veritesting region
   */
  private boolean populateOutputs(HashSet<Expression> outputVars,
                                  HashMap<Expression, Expression> holeHashMap,
                                  StackFrame stackFrame, ThreadInfo ti) {
    Iterator iterator = outputVars.iterator();
    while(iterator.hasNext()) {
      Expression expression = (Expression) iterator.next(), finalValue;
      assert(expression instanceof HoleExpression);
      HoleExpression holeExpression = (HoleExpression) expression;
      assert(holeHashMap.containsKey(holeExpression));
      finalValue = holeHashMap.get(holeExpression);
      switch(holeExpression.getHoleType()) {
        case LOCAL_OUTPUT:
          stackFrame.setSlotAttr(holeExpression.getLocalStackSlot(), GreenToSPFExpression(finalValue));
          break;
        case FIELD_OUTPUT:
          HoleExpression.FieldInfo fieldInfo = holeExpression.getFieldInfo();
          assert(fieldInfo != null);
          fillFieldOutputHole(ti, stackFrame, fieldInfo, GreenToSPFExpression(finalValue));
          break;
      }
    }
    return true;
  }

  private gov.nasa.jpf.symbc.numeric.Expression GreenToSPFExpression(Expression greenExpression) {
    GreenToSPFTranslator toSPFTranslator = new GreenToSPFTranslator();
    return toSPFTranslator.translate(greenExpression);
  }

  /*
  Walk the CNLIE expression, looking for holes (which will always be at the leaf nodes), and ensure that all holes
  are filled in
   */
  private Expression fillASTHoles(Expression holeExpression,
                                         HashMap<Expression, Expression> holeHashMap) {
    if(holeExpression instanceof HoleExpression && ((HoleExpression)holeExpression).isHole()) {
      //assert(holeHashMap.containsKey(holeExpression));
      if(!holeHashMap.containsKey(holeExpression)) {
        System.out.println("fillASTHoles does not know how to fill hole " + holeExpression.toString());
        assert(false);
      }
      Expression ret = holeHashMap.get(holeExpression);
      if(ret instanceof Operation) {
        Operation oldOperation = (Operation) ret;
        Operation newOperation = new Operation(oldOperation.getOperator(),
                fillASTHoles(oldOperation.getOperand(0), holeHashMap),
                fillASTHoles(oldOperation.getOperand(1), holeHashMap));
        return newOperation;
      }
      return ret;
    }
    if(holeExpression instanceof Operation) {
      Operation oldOperation = (Operation) holeExpression;
      Operation newOperation = new Operation(oldOperation.getOperator(),
              fillASTHoles(oldOperation.getOperand(0), holeHashMap),
              fillASTHoles(oldOperation.getOperand(1), holeHashMap));
      return newOperation;
    }
    return holeExpression;
  }

  /*
  Load from local variable stack slots IntegerExpression objects and store them into holeHashMap
   */
  private FillHolesOutput fillHoles(
          HashMap<Expression, Expression> holeHashMap,
          InstructionInfo instructionInfo,
          StackFrame stackFrame,
          ThreadInfo ti) {
    HashMap<Expression, Expression> retHoleHashMap = new HashMap<>();
    Operation additionalAST = null;
    for(HashMap.Entry<Expression, Expression> entry : holeHashMap.entrySet()) {
      Expression key = entry.getKey(), finalValueGreen;
      gov.nasa.jpf.symbc.numeric.Expression finalValueSPF;
      assert (key instanceof HoleExpression);
      HoleExpression keyHoleExpression = (HoleExpression) key;
      assert (keyHoleExpression.isHole());
      switch (keyHoleExpression.getHoleType()) {
        case LOCAL_INPUT:
          finalValueSPF =
                  (gov.nasa.jpf.symbc.numeric.Expression) stackFrame.getLocalAttr(keyHoleExpression.getLocalStackSlot());
          if (finalValueSPF == null)
            finalValueSPF = new IntegerConstant(stackFrame.getLocalVariable(keyHoleExpression.getLocalStackSlot()));
          finalValueGreen = SPFToGreenExpr(finalValueSPF);
          retHoleHashMap.put(keyHoleExpression, finalValueGreen);
          break;
        case LOCAL_OUTPUT:
        case FIELD_OUTPUT:
        case INTERMEDIATE:
          finalValueSPF =
                  makeSymbolicInteger(keyHoleExpression.getHoleVarName() + pathLabelCount);
          finalValueGreen = SPFToGreenExpr(finalValueSPF);
          retHoleHashMap.put(keyHoleExpression, finalValueGreen);
          break;
        case FIELD_INPUT:
          HoleExpression.FieldInfo fieldInfo = keyHoleExpression.getFieldInfo();
          assert (fieldInfo != null);
          finalValueSPF = fillFieldInputHole(ti, stackFrame, fieldInfo);
          assert (finalValueSPF != null);
          finalValueGreen = SPFToGreenExpr(finalValueSPF);
          retHoleHashMap.put(keyHoleExpression, finalValueGreen);
          break;
        case NONE:
          System.out.println("expression marked as hole with NONE hole type: " +
                  keyHoleExpression.toString());
          assert (false);
          break;
        case CONDITION:
          finalValueGreen = instructionInfo.getCondition();
          assert (finalValueGreen != null);
          retHoleHashMap.put(keyHoleExpression, finalValueGreen);
          break;
        case NEGCONDITION:
          finalValueGreen = instructionInfo.getNegCondition();
          assert (finalValueGreen != null);
          retHoleHashMap.put(keyHoleExpression, finalValueGreen);
          break;
      }
    }
    for(HashMap.Entry<Expression, Expression> entry : holeHashMap.entrySet()) {
      Expression key = entry.getKey(), greenExpr = null;
      gov.nasa.jpf.symbc.numeric.Expression spfExpr;
      assert(key instanceof HoleExpression);
      HoleExpression keyHoleExpression = (HoleExpression) key;
      assert(keyHoleExpression.isHole());
      switch(keyHoleExpression.getHoleType()) {
        case INVOKEVIRTUAL:
          InvokeVirtualInfo callSiteInfo = keyHoleExpression.getInvokeVirtualInfo();
          Expression callingObject = retHoleHashMap.get(callSiteInfo.paramList.get(0));
          ClassInfo ci = ti.getClassInfo(((IntConstant)callingObject).getValue());
          //Change the class name based on the call site object reference
          callSiteInfo.className = ci.getName();
          //If there exists a invokeVirtual for a method that we weren't able to summarize, skip veritesting
          if(!veritestingRegions.containsKey(callSiteInfo.className+"."+callSiteInfo.methodName+"#0"))
            return null;
          //All holes in callSiteInfo.paramList will also be present in holeHashmap and will be filled up here
          for(Expression h: callSiteInfo.paramList) {
            if(h instanceof HoleExpression) assert(holeHashMap.containsKey(h));
          }
          VeritestingRegion methodSummary = veritestingRegions.get(callSiteInfo.className+"."+callSiteInfo.methodName+"#0");
          HashMap<Expression, Expression> methodHoles = methodSummary.getHoleHashMap();
          ArrayList<Expression> paramEqList = new ArrayList<>();
          for(HashMap.Entry<Expression, Expression> entry1 : methodHoles.entrySet()) {
            Expression methodKeyExpr = entry1.getKey();
            assert(methodKeyExpr instanceof HoleExpression);
            HoleExpression methodKeyHole = (HoleExpression) methodKeyExpr;
            assert(methodKeyHole.isHole());
            switch(methodKeyHole.getHoleType()) {
              //LOCAL_INPUTs can be mapped to parameters at the call site, but non-parameter local inputs cannot
              // in other words, we cannot support summarization of functions that create something on the stack
              case LOCAL_INPUT:
                //local inputs used in method summary have to come from the filled-up holes in paramList
                if (methodKeyHole.getLocalStackSlot() < callSiteInfo.paramList.size()) {
                  int methodLocalStackSlot = methodKeyHole.getLocalStackSlot();
                  //int callSiteLocalStackSlot = ((HoleExpression)callSiteInfo.paramList[methodLocalStackSlot]).getLocalStackSlot();
                  //methodKeyHole.setLocalStackSlot(callSiteLocalStackSlot);
                  retHoleHashMap.put(methodKeyHole, retHoleHashMap.get(callSiteInfo.paramList.get(methodLocalStackSlot)));
                  paramEqList.add(new Operation(Operation.Operator.EQ,
                          methodKeyHole,
                          callSiteInfo.paramList.get(methodLocalStackSlot)));
                } else {
                  System.out.println("Don't know how to fill method summary hole: " + methodKeyHole);
                  return null;
                }
                break;
              case CONDITION:
                System.out.println("unsupported condition hole in method summary");
                assert(false);
                break;
              case NEGCONDITION:
                System.out.println("unsupported negCondition hole in method summary");
                assert(false);
                break;
              case INVOKEVIRTUAL:
                System.out.println("unsupported invokeVirtual hole in method summary");
                assert(false);
                break;
              case LOCAL_OUTPUT:
                System.out.println("unsupported local variable output in method summary");
                assert(false);
                break;
              case INTERMEDIATE:
                spfExpr = makeSymbolicInteger(methodKeyHole.getHoleVarName() + pathLabelCount);
                greenExpr = SPFToGreenExpr(spfExpr);
                retHoleHashMap.put(methodKeyHole, greenExpr);
                break;
              case NONE:
                break;
              case FIELD_INPUT:
                HoleExpression.FieldInfo fieldInfo = methodKeyHole.getFieldInfo();
                //The object reference where this field lives HAS to be present in the current method's stack frame
                //and we populate that stack slot in fieldInfo for fillFieldInputHole to use
                assert(((HoleExpression)callSiteInfo.paramList.get(0)).getHoleType() == HoleExpression.HoleType.LOCAL_INPUT ||
                        ((HoleExpression)callSiteInfo.paramList.get(0)).getHoleType() == HoleExpression.HoleType.LOCAL_OUTPUT);
                int callSiteStackSlot = ((HoleExpression) callSiteInfo.paramList.get(0)).getLocalStackSlot();
                fieldInfo.callSiteStackSlot = callSiteStackSlot;
                //retHoleHashMap.put(fieldInfo.use, retHoleHashMap.get(callSiteInfo.paramList[0]));
                //paramEqList.add(new Operation(Operation.Operator.EQ, fieldInfo.use, callSiteInfo.paramList[0]));
                assert (fieldInfo != null);
                spfExpr = fillFieldInputHole(ti, stackFrame, fieldInfo);
                assert (spfExpr != null);
                greenExpr = SPFToGreenExpr(spfExpr);
                retHoleHashMap.put(methodKeyHole, greenExpr);
                break;
              case FIELD_OUTPUT:
                fieldInfo = methodKeyHole.getFieldInfo();
                //The object reference where this field lives HAS to be present in the current method's stack frame
                //and we populate that stack slot in fieldInfo for fillFieldOutputHole to use later
                fieldInfo.callSiteStackSlot = ((HoleExpression)callSiteInfo.paramList.get(0)).getLocalStackSlot();
                methodKeyHole.setFieldInfo(fieldInfo.className, fieldInfo.fieldName,
                        fieldInfo.localStackSlot, fieldInfo.callSiteStackSlot);
                break;
              default:
                System.out.println("expression marked with unknown hole type: " +
                        keyHoleExpression.toString());
                assert(false);
                return null;
            }
          }
          Operation retValEq = new Operation(Operation.Operator.EQ, methodSummary.retVal, keyHoleExpression);
          Operation mappingOperation = retValEq;
          for(int i=0; i < paramEqList.size(); i++) {
            //paramList.length-1 because there won't be a constraint created for the object reference which is always
            //parameter 0
            mappingOperation = new Operation(Operation.Operator.EQ, mappingOperation, paramEqList.get(i));
          }
          if(methodSummary.getSummaryExpression() != null)
            mappingOperation = new Operation(Operation.Operator.AND, mappingOperation, methodSummary.getSummaryExpression());
          if(additionalAST != null) additionalAST = new Operation(Operation.Operator.AND, additionalAST, mappingOperation);
          else additionalAST = mappingOperation;
          Expression finalValueGreen = SPFToGreenExpr(makeSymbolicInteger(keyHoleExpression.getHoleVarName() + pathLabelCount));
          retHoleHashMap.put(keyHoleExpression, finalValueGreen);
          break;
      }
    }
    return new FillHolesOutput(retHoleHashMap, additionalAST);
  }

  gov.nasa.jpf.symbc.numeric.Expression fillFieldInputHole(
          ThreadInfo ti,
          StackFrame stackFrame,
          HoleExpression.FieldInfo fieldInputInfo) {
    //get the object reference from fieldInputInfo.use's local stack slot if not from the call site stack slot
    int stackSlot = fieldInputInfo.callSiteStackSlot;
    if(stackSlot == -1) stackSlot = fieldInputInfo.localStackSlot;
    int objRef = stackFrame.getLocalVariable(stackSlot);
    if (objRef == 0) {
      System.out.println("java.lang.NullPointerException" + "referencing field '" +
              fieldInputInfo.fieldName+ "' on null object");
      assert(false);
    } else {
      ElementInfo eiFieldOwner = ti.getElementInfo(objRef);
      FieldInfo fieldInfo = null;
      ClassInfo ci = ClassLoaderInfo.getCurrentResolvedClassInfo(fieldInputInfo.className);
      if (ci != null) {
        fieldInfo = ci.getInstanceField(fieldInputInfo.fieldName);
      }
      if (fieldInfo == null) {
         System.out.println("java.lang.NoSuchFieldError" + "referencing field '" + fieldInputInfo.fieldName
                + "' in " + eiFieldOwner);
         assert(false);
      } else {
        Object fieldAttr = eiFieldOwner.getFieldAttr(fieldInfo);
        if(fieldAttr != null) {
          return (gov.nasa.jpf.symbc.numeric.Expression) fieldAttr;
        } else {
          if (fieldInfo.getStorageSize() == 1) {
            return (gov.nasa.jpf.symbc.numeric.Expression) new IntegerConstant(eiFieldOwner.get1SlotField(fieldInfo));
          } else {
            return (gov.nasa.jpf.symbc.numeric.Expression) new IntegerConstant(eiFieldOwner.get2SlotField(fieldInfo));
          }
        }
      }
    }
    return null;
  }

  void fillFieldOutputHole(ThreadInfo ti,
                                        StackFrame stackFrame,
                                        HoleExpression.FieldInfo fieldInputInfo,
                                        gov.nasa.jpf.symbc.numeric.Expression finalValue) {
    int stackSlot = fieldInputInfo.callSiteStackSlot;
    if(stackSlot == -1) stackSlot = fieldInputInfo.localStackSlot;
    int objRef = stackFrame.getLocalVariable(stackSlot);
    if (objRef == 0) {
      System.out.println("java.lang.NullPointerException" + "referencing field '" +
              fieldInputInfo.fieldName+ "' on null object");
      assert(false);
    } else {
      ElementInfo eiFieldOwner = ti.getModifiableElementInfo(objRef);
      FieldInfo fieldInfo = null;
      ClassInfo ci = ClassLoaderInfo.getCurrentResolvedClassInfo(fieldInputInfo.className);
      if (ci != null) {
        fieldInfo = ci.getInstanceField(fieldInputInfo.fieldName);
      }
      if (fieldInfo == null) {
        System.out.println("java.lang.NoSuchFieldError" + "referencing field '" + fieldInputInfo.fieldName
                + "' in " + eiFieldOwner);
        assert(false);
      } else {
        int fieldSize = fieldInfo.getStorageSize();
        if (fieldSize == 1) {
          eiFieldOwner.set1SlotField(fieldInfo, 0); // field value should not matter (I think)
          eiFieldOwner.setFieldAttr(fieldInfo, finalValue);
        } else {
          eiFieldOwner.set2SlotField(fieldInfo, 0); // field value should not matter (I think)
          eiFieldOwner.setFieldAttr(fieldInfo, finalValue);
        }
      }
    }
  }

  private class InstructionInfo {
    private ThreadInfo ti;
    private int numOperands;
    private Operation.Operator trueComparator, falseComparator;
    private Expression condition, negCondition;

    public Expression getCondition() { return condition; }

    public Expression getNegCondition() { return negCondition; }

    public InstructionInfo(ThreadInfo ti) {
      this.ti = ti;
    }

    public int getNumOperands() {
      return numOperands;
    }

    public Operation.Operator getTrueComparator() {
      return trueComparator;
    }

    public Operation.Operator getFalseComparator() {
      return falseComparator;
    }

    public InstructionInfo invoke() {
      switch(ti.getTopFrame().getPC().getMnemonic()) {
        case "ifeq" :
          numOperands = 1;
          trueComparator = Operation.Operator.EQ; falseComparator = Operation.Operator.NE;
          break;
        case "ifne":
          trueComparator = Operation.Operator.NE; falseComparator = Operation.Operator.EQ;
          numOperands = 1;
          break;
        case "iflt":
          trueComparator = Operation.Operator.LT; falseComparator = Operation.Operator.GE;
          numOperands = 1;
          break;
        case "ifle":
          trueComparator = Operation.Operator.LE; falseComparator = Operation.Operator.GT;
          numOperands = 1;
          break;
        case "ifgt":
          trueComparator = Operation.Operator.GT; falseComparator = Operation.Operator.LE;
          numOperands = 1;
          break;
        case "ifge":
          trueComparator = Operation.Operator.GE; falseComparator = Operation.Operator.LT;
          numOperands = 1;
          break;
        case "ifnull":
          trueComparator = Operation.Operator.EQ; falseComparator = Operation.Operator.NE;
          numOperands = 1;
          break;
        case "ifnonnull":
          trueComparator = Operation.Operator.EQ; falseComparator = Operation.Operator.NE;
          numOperands = 1;
          break;
        default :
          return null;
      }
      IntegerExpression operand1 = null, operand2 = null;
      operand1 = (IntegerExpression) ti.getTopFrame().getOperandAttr();
      boolean isConcreteCondition = true;
      if(operand1 == null) {
        operand1 = new IntegerConstant(ti.getTopFrame().peek());
      } else isConcreteCondition = false;
      if(numOperands == 2) {
        operand2 = (IntegerExpression) ti.getTopFrame().getOperandAttr(1);
        if(operand2 != null) isConcreteCondition = false;
        else operand2 = new IntegerConstant(ti.getTopFrame().peek(1));
      } else operand2 = new IntegerConstant(0);
      if(isConcreteCondition) { condition = null; negCondition = null; }
      else {
        condition = new Operation(trueComparator, SPFToGreenExpr(operand1), SPFToGreenExpr(operand2));
        negCondition = new Operation(falseComparator, SPFToGreenExpr(operand1), SPFToGreenExpr(operand2));
      }
      return this;
    }

  }

  Expression SPFToGreenExpr(gov.nasa.jpf.symbc.numeric.Expression spfExp) {
    SolverTranslator.Translator toGreenTranslator = new SolverTranslator.Translator();
    spfExp.accept(toGreenTranslator);
    return toGreenTranslator.getExpression();
  }

  /*public IntegerExpression constantFold(IntegerExpression integerExpression) {
    if(integerExpression instanceof IntegerConstant) return integerExpression;
    if(integerExpression instanceof ComplexNonLinearIntegerExpression) {
      ComplexNonLinearIntegerExpression cnlie = (ComplexNonLinearIntegerExpression) integerExpression;
      if (cnlie.getLeft() instanceof IntegerConstant && cnlie.getRight() instanceof IntegerConstant) {
        int left = ((IntegerConstant) cnlie.getLeft()).value();
        int right = ((IntegerConstant) cnlie.getRight()).value();
        int result = 0;
        switch (cnlie.getOperator()) {
          case DIV:
            result = left / right;
            break;
          case MUL:
            result = left * right;
            break;
          case MINUS:
            result = left - right;
            break;
          case PLUS:
            result = left + right;
            break;
          case CMP:
            result = Integer.compare(left, right);
            break;
          case AND:
            result = left & right;
            break;
          case OR:
            result = left | right;
            break;
          case XOR:
            result = left ^ right;
            break;
          case SHIFTL:
            result = left << right;
            break;
          case SHIFTR:
            result = left >> right;
            break;
          case SHIFTUR:
            result = left >>> right;
            break;
          case REM:
            result = left % right;
            break;
          case NONE_OP:
            switch (cnlie.getComparator()) {
              case EQ:
                result = (left == right) ? 1 : 0;
                break;
              case NE:
                result = (left != right) ? 1 : 0;
                break;
              case LT:
                result = (left < right) ? 1 : 0;
                break;
              case LE:
                result = (left <= right) ? 1 : 0;
                break;
              case GT:
                result = (left > right) ? 1 : 0;
                break;
              case GE:
                result = (left >= right) ? 1 : 0;
                break;
              case LOGICAL_AND:
                result = ((left != 0) && (right != 0)) ? 1 : 0;
                break;
              case LOGICAL_OR:
                result = ((left != 0) || (right != 0)) ? 1 : 0;
                break;
              case NONE_CMP:
                System.out.println("constantFold found NONE_OP and NONE_CMP");
                assert(false);
                break;
              default:
                System.out.println("constantFold found NONE_OP and undefined comparator (" + cnlie.getComparator() + ")");
                assert(false);
                break;
            }
            break;
          default:
            System.out.println("constantFold found undefined operator (" + cnlie.getOperator() + ")");
            assert (false);
        }
        return new IntegerConstant(result);
      }
      cnlie.setLeft(constantFold(cnlie.getLeft()));
      cnlie.setRight(constantFold(cnlie.getRight()));
      if(cnlie.getLeft() instanceof IntegerConstant) {
        if(cnlie.getRight() instanceof IntegerConstant) {
          if(cnlie.getOperator() == NONE_OP) {
            return constantFold(new ComplexNonLinearIntegerExpression(cnlie.getLeft(), cnlie.getComparator(), cnlie.getRight()));
          }
          if(cnlie.getComparator() == NONE_CMP) {
            return constantFold(new ComplexNonLinearIntegerExpression(cnlie.getLeft(), cnlie.getOperator(), cnlie.getRight()));
          }
        }
      }
    }
    return integerExpression;
  }*/

  // TestPathsSimple listener for testMe3
  /*public void executeInstruction_TestPathsSimple_testMe3(VM vm, ThreadInfo ti, Instruction instructionToExecute) {
    int x_slot_index = 1, y_slot_index = 2;
    // int af_slot_index = 3, bf_slot_index = 4;
    int a_slot_index = 3, b_slot_index = 4;
    int startInsn = 41, endInsn = 71;
    if(ti.getTopFrame().getPC().getPosition() == startInsn &&
       ti.getTopFrame().getMethodInfo().getName().equals("testMe3") &&
       ti.getTopFrame().getClassInfo().getName().equals("TestPathsSimple")) {
      StackFrame sf = ti.getTopFrame();
      System.out.println("time to start veritesting for " +
       ti.getTopFrame().getMethodInfo().getName());
      System.out.println("topPos = "+sf.getTopPos());

      SymbolicInteger x_v = (SymbolicInteger) sf.getLocalAttr(x_slot_index);
      if(x_v == null) System.out.println("failed to get x expr");
      SymbolicInteger y_v = (SymbolicInteger) sf.getLocalAttr(y_slot_index);
      if(y_v == null) System.out.println("failed to get y expr");

      SymbolicInteger a_v = makeSymbolicInteger("a_final");
      SymbolicInteger b_v = makeSymbolicInteger("b_final");
      // IntegerExpression a_v = (IntegerExpression) sf.getLocalAttr(af_slot_index);
      // if(a_v == null) System.out.println("failed to get a_final expr");
      // IntegerExpression b_v = (IntegerExpression) sf.getLocalAttr(bf_slot_index);
      // if(b_v == null) System.out.println("failed to get b_final expr");

      // PathCondition pc = null;
      // pc = getPC(vm, ti, instructionToExecute, pc);
      ChoiceGenerator<?> cg;

			// if (!ti.isFirstStepInsn()) { // first time around
      //   System.out.println("first time around");
			// 	cg = new PCChoiceGenerator(2);
      //   ((PCChoiceGenerator)cg).setOffset(instructionToExecute.getPosition());
      //   ((PCChoiceGenerator)cg).setMethodName(ti.getTopFrame().getMethodInfo().getFullName());
			// 	ti.getVM().getSystemState().setNextChoiceGenerator(cg);
			// 	return ;
			// } else {  // this is what really returns results
				cg = ti.getVM().getSystemState().getChoiceGenerator();
				assert (cg instanceof PCChoiceGenerator) : "expected PCChoiceGenerator, got: " + cg;
			// }

			PathCondition pc;

			// pc is updated with the pc stored in the choice generator above
			// get the path condition from the
			// previous choice generator of the same type
			ChoiceGenerator<?> prev_cg = cg.getPreviousChoiceGeneratorOfType(PCChoiceGenerator.class);


			if (prev_cg == null)
				pc = new PathCondition();
			else
				pc = ((PCChoiceGenerator)prev_cg).getCurrentPC();

			assert pc != null;
      // Generate symbolic expressions to unroll lines 39-42 of TestPaths.java
      pc._addDet(new ComplexNonLinearIntegerConstraint(
            new ComplexNonLinearIntegerExpression(
              new ComplexNonLinearIntegerExpression(
                new ComplexNonLinearIntegerExpression(x_v, LE, new IntegerConstant(800)),
                LOGICAL_AND,
                new ComplexNonLinearIntegerExpression(a_v, EQ, new IntegerConstant(-1))),
              LOGICAL_OR,
              new ComplexNonLinearIntegerExpression(
                new ComplexNonLinearIntegerExpression(x_v, GT, new IntegerConstant(800)),
                LOGICAL_AND,
                new ComplexNonLinearIntegerExpression(a_v, EQ, new IntegerConstant(1))))));

      pc._addDet(new ComplexNonLinearIntegerConstraint(
            new ComplexNonLinearIntegerExpression(
              new ComplexNonLinearIntegerExpression(
                new ComplexNonLinearIntegerExpression(y_v, LE, new IntegerConstant(1200)),
                LOGICAL_AND,
                new ComplexNonLinearIntegerExpression(b_v, EQ, new IntegerConstant(-1))),
              LOGICAL_OR,
              new ComplexNonLinearIntegerExpression(
                new ComplexNonLinearIntegerExpression(y_v, GT, new IntegerConstant(1200)),
                LOGICAL_AND,
                new ComplexNonLinearIntegerExpression(b_v, EQ, new IntegerConstant(1))))));
      ((PCChoiceGenerator) cg).setCurrentPC(pc);

      // Assign a', b' (aka a_final, b_final) back into a, b respectively
      int a_val = sf.getSlot(a_slot_index);
      sf.setSlotAttr(a_slot_index, a_v);
      int b_val = sf.getSlot(b_slot_index);
      sf.setSlotAttr(b_slot_index, b_v);
      ((PCChoiceGenerator) ti.getVM().getSystemState().getChoiceGenerator()).setCurrentPC(pc);

      Instruction insn=instructionToExecute;
      while(insn.getPosition() < endInsn)
        insn = insn.getNext();
      ti.setNextPC(insn);
    }
    // if(ti.getTopFrame().getPC().getPosition() == 71 &&
    //    ti.getTopFrame().getMethodInfo().getName().equals("testMe3") &&
    //    ti.getTopFrame().getClassInfo().getName().equals("TestPathsSimple")) {
    //   System.out.println("At later offset, PC = " + getPC(vm, ti, instructionToExecute, null));
    // }

  }*/

  // Veritesting listener for testMe4 method
  /*public void executeInstruction_VeritestingPerf_testMe4(VM vm, ThreadInfo ti, Instruction instructionToExecute) {
    int sum_slot_index = 3;
    int startInsn = 61, endInsn = 80;
    if(ti.getTopFrame().getPC().getPosition() == startInsn &&
       ti.getTopFrame().getMethodInfo().getName().equals("testMe4") &&
       ti.getTopFrame().getClassInfo().getName().equals("VeritestingPerf")) {
      StackFrame sf = ti.getTopFrame();
      System.out.println("time to start veritesting for " +
       ti.getTopFrame().getMethodInfo().getName());

      IntegerExpression x_v = (IntegerExpression) sf.getOperandAttr(0);
      if(x_v == null) System.out.println("failed to get x expr");
      IntegerExpression sum_v = (IntegerExpression) sf.getLocalAttr(sum_slot_index);
      if(sum_v == null) System.out.println("failed to get sum expr");

      SymbolicInteger sum_new = makeSymbolicInteger("sum_new"+sumId);
      sumId++;
      PathCondition pc = null;
      pc = ((PCChoiceGenerator) ti.getVM().getSystemState().getChoiceGenerator()).getCurrentPC();

      // LogicalORLinearIntegerConstraints lolic = new LogicalORLinearIntegerConstraints();
      // lolic.addToList(
      //     new LinearIntegerConstraint(
      //       new ComplexNonLinearIntegerExpression(x_v, LT, new IntegerConstant(0)),
      //     LOGICAL_AND,
      //       new ComplexNonLinearIntegerExpression(sum_new, EQ, new IntegerConstant(-1))));
      // lolic.addToList(
      //     new LinearIntegerConstraint(
      //       new ComplexNonLinearIntegerExpression(x_v, GT, new IntegerConstant(0)),
      //     LOGICAL_AND,
      //       new ComplexNonLinearIntegerExpression(sum_new, EQ, new IntegerConstant(1))));

      // lolic.addToList(
      //     new LinearIntegerConstraint(
      //       new ComplexNonLinearIntegerExpression(x_v, EQ, new IntegerConstant(0)),
      //     LOGICAL_AND,
      //       new ComplexNonLinearIntegerExpression(sum_new, EQ, new IntegerConstant(0))));

      // pc._addDet(lolic);

      // pc._addDet(EQ, sum_new,
      //   new BinaryNonLinearIntegerExpression(x_v, CMP, new IntegerConstant(0)));

      ComplexNonLinearIntegerExpression cnlie1 = new ComplexNonLinearIntegerExpression(
          new ComplexNonLinearIntegerExpression(x_v, LT, new IntegerConstant(0)),
          LOGICAL_AND,
          new ComplexNonLinearIntegerExpression(sum_new, EQ, new IntegerConstant(-1)) );
      ComplexNonLinearIntegerExpression cnlie2 = new ComplexNonLinearIntegerExpression(
          new ComplexNonLinearIntegerExpression(x_v, GT, new IntegerConstant(0)),
          LOGICAL_AND,
          new ComplexNonLinearIntegerExpression(sum_new, EQ, new IntegerConstant(1)) );
      ComplexNonLinearIntegerExpression cnlie3 = new ComplexNonLinearIntegerExpression(
          new ComplexNonLinearIntegerExpression(x_v, EQ, new IntegerConstant(0)),
          LOGICAL_AND,
          new ComplexNonLinearIntegerExpression(sum_new, EQ, new IntegerConstant(0)) );
      ComplexNonLinearIntegerExpression cnlie1_2 =
        new ComplexNonLinearIntegerExpression(cnlie1, LOGICAL_OR, cnlie2);
      ComplexNonLinearIntegerExpression cnlie1_2_3 =
        new ComplexNonLinearIntegerExpression(cnlie1_2, LOGICAL_OR, cnlie3);

      pc._addDet(new ComplexNonLinearIntegerConstraint(cnlie1_2_3));

      ((PCChoiceGenerator) ti.getVM().getSystemState().getChoiceGenerator()).setCurrentPC(pc);

      if(sumId > 1)
        sf.setSlotAttr(sum_slot_index, new BinaryNonLinearIntegerExpression(sum_v, PLUS, sum_new));
      else
        sf.setSlotAttr(sum_slot_index, sum_new);
      sf.pop(); //pops off the x expr

      Instruction insn=instructionToExecute;
      while(insn.getPosition() < endInsn)
        insn = insn.getNext();
      ti.setNextPC(insn);
    }
  }*/

  // TestPaths listener
  /*public void executeInstruction_TestPaths(VM vm, ThreadInfo ti, Instruction instructionToExecute) {
    int x_slot_index = 1, y_slot_index = 2;
    //int a_final_slot_index = 3, b_final_slot_index = 4;
    int a_slot_index = 3, b_slot_index = 4;
    int startInsn = 7, endInsn = 46;
    if(ti.getTopFrame().getPC().getPosition() == startInsn &&
       ti.getTopFrame().getMethodInfo().getName().equals("testMe3") &&
       ti.getTopFrame().getClassInfo().getName().equals("TestPaths")) {
      StackFrame sf = ti.getTopFrame();
      System.out.println("time to start veritesting for " +
       ti.getTopFrame().getMethodInfo().getName());
      System.out.println("topPos = "+sf.getTopPos());

      IntegerExpression x_v = (IntegerExpression) sf.getLocalAttr(x_slot_index);
      if(x_v == null) System.out.println("failed to get x expr");
      IntegerExpression y_v = (IntegerExpression) sf.getLocalAttr(y_slot_index);
      if(y_v == null) System.out.println("failed to get y expr");
      SymbolicInteger a_v = makeSymbolicInteger("a_final");
      SymbolicInteger b_v = makeSymbolicInteger("b_final");
      // IntegerExpression a_v = (IntegerExpression) sf.getLocalAttr(a_final_slot_index);
      // if(a_v == null) System.out.println("failed to get a_final expr");
      // IntegerExpression b_v = (IntegerExpression) sf.getLocalAttr(b_final_slot_index);
      // if(b_v == null) System.out.println("failed to get b_final expr");

      PathCondition pc = null;
      pc = getPC(vm, ti, instructionToExecute, pc);

      // Generate symbolic expressions to unroll lines 40-45 of TestPaths.java
      pc._addDet(EQ, a_v, new BinaryNonLinearIntegerExpression(
            x_v, CMP, new IntegerConstant(0)));
      pc._addDet(EQ, b_v, new BinaryNonLinearIntegerExpression(
            y_v, CMP, new IntegerConstant(0)));

      // Assign a', b' (aka a_final, b_final) back into a, b respectively
      int a_val = sf.getSlot(a_slot_index);
      sf.setSlotAttr(a_slot_index, a_v);
      int b_val = sf.getSlot(b_slot_index);
      sf.setSlotAttr(b_slot_index, b_v);

      Instruction insn=instructionToExecute;
      while(insn.getPosition() < endInsn)
        insn = insn.getNext();
      ti.setNextPC(insn);
    }
  }
  public void TestPathsSimple_testMe3_VT_46_58
 (VM vm, ThreadInfo ti, Instruction instructionToExecute) {
  if(ti.getTopFrame().getPC().getPosition() == 46 &&
     ti.getTopFrame().getMethodInfo().getName().equals("testMe3") &&
     ti.getTopFrame().getClassInfo().getName().equals("TestPathsSimple")) {
    StackFrame sf = ti.getTopFrame();
    SymbolicInteger x = (SymbolicInteger) sf.getLocalAttr(1);
    SymbolicInteger a_2 = makeSymbolicInteger("a_2");
    SymbolicInteger a_1 = makeSymbolicInteger("a_1");
    SymbolicInteger a_3 = makeSymbolicInteger("a_3");
    SymbolicInteger pathLabel0 = makeSymbolicInteger("pathLabel0");
    PathCondition pc;
    pc = ((PCChoiceGenerator) ti.getVM().getSystemState().getChoiceGenerator()).getCurrentPC();
    pc._addDet(new ComplexNonLinearIntegerConstraint(
    new ComplexNonLinearIntegerExpression(new ComplexNonLinearIntegerExpression(new ComplexNonLinearIntegerExpression(new ComplexNonLinearIntegerExpression(x, GT, new IntegerConstant(800)), LOGICAL_AND, new ComplexNonLinearIntegerExpression(new ComplexNonLinearIntegerExpression(a_1, EQ, new IntegerConstant(-1)), LOGICAL_AND, new ComplexNonLinearIntegerExpression(pathLabel0, EQ, new IntegerConstant(1)))), LOGICAL_OR, new ComplexNonLinearIntegerExpression(new ComplexNonLinearIntegerExpression(x, LE, new IntegerConstant(800)), LOGICAL_AND, new ComplexNonLinearIntegerExpression(new ComplexNonLinearIntegerExpression(a_2, EQ, new IntegerConstant(1)), LOGICAL_AND, new ComplexNonLinearIntegerExpression(pathLabel0, EQ, new IntegerConstant(2))))), LOGICAL_AND, new ComplexNonLinearIntegerExpression(new ComplexNonLinearIntegerExpression(new ComplexNonLinearIntegerExpression(pathLabel0, EQ, new IntegerConstant(1)), LOGICAL_AND, new ComplexNonLinearIntegerExpression(a_3, EQ, a_1)), LOGICAL_OR, new ComplexNonLinearIntegerExpression(new ComplexNonLinearIntegerExpression(pathLabel0, EQ, new IntegerConstant(2)), LOGICAL_AND, new ComplexNonLinearIntegerExpression(a_3, EQ, a_2))))));
    sf.setSlotAttr(4, a_3);
    Instruction insn=instructionToExecute;
    while(insn.getPosition() < 58)
      insn = insn.getNext();
    sf.pop(); sf.pop();
    ((PCChoiceGenerator) ti.getVM().getSystemState().getChoiceGenerator()).setCurrentPC(pc);
    ti.setNextPC(insn);
  }
}

  public void TestPathsSimple_testMe3_VT_62_74
          (VM vm, ThreadInfo ti, Instruction instructionToExecute) {
    if(ti.getTopFrame().getPC().getPosition() == 62 &&
            ti.getTopFrame().getMethodInfo().getName().equals("testMe3") &&
            ti.getTopFrame().getClassInfo().getName().equals("TestPathsSimple")) {
      StackFrame sf = ti.getTopFrame();
      SymbolicInteger y = (SymbolicInteger) sf.getLocalAttr(2);
      SymbolicInteger b_1 = makeSymbolicInteger("b_1");
      SymbolicInteger b_2 = makeSymbolicInteger("b_2");
      SymbolicInteger b_3 = makeSymbolicInteger("b_3");
      SymbolicInteger pathLabel1 = makeSymbolicInteger("pathLabel1");
      PathCondition pc;
      pc = ((PCChoiceGenerator) ti.getVM().getSystemState().getChoiceGenerator()).getCurrentPC();
      pc._addDet(new ComplexNonLinearIntegerConstraint(
              new ComplexNonLinearIntegerExpression(new ComplexNonLinearIntegerExpression(new ComplexNonLinearIntegerExpression(new ComplexNonLinearIntegerExpression(y, GT, new IntegerConstant(1200)), LOGICAL_AND, new ComplexNonLinearIntegerExpression(new ComplexNonLinearIntegerExpression(b_1, EQ, new IntegerConstant(-1)), LOGICAL_AND, new ComplexNonLinearIntegerExpression(pathLabel1, EQ, new IntegerConstant(3)))), LOGICAL_OR, new ComplexNonLinearIntegerExpression(new ComplexNonLinearIntegerExpression(y, LE, new IntegerConstant(1200)), LOGICAL_AND, new ComplexNonLinearIntegerExpression(new ComplexNonLinearIntegerExpression(b_2, EQ, new IntegerConstant(1)), LOGICAL_AND, new ComplexNonLinearIntegerExpression(pathLabel1, EQ, new IntegerConstant(4))))), LOGICAL_AND, new ComplexNonLinearIntegerExpression(new ComplexNonLinearIntegerExpression(new ComplexNonLinearIntegerExpression(pathLabel1, EQ, new IntegerConstant(3)), LOGICAL_AND, new ComplexNonLinearIntegerExpression(b_3, EQ, b_1)), LOGICAL_OR, new ComplexNonLinearIntegerExpression(new ComplexNonLinearIntegerExpression(pathLabel1, EQ, new IntegerConstant(4)), LOGICAL_AND, new ComplexNonLinearIntegerExpression(b_3, EQ, b_2))))));
      sf.setSlotAttr(5, b_3);
      Instruction insn=instructionToExecute;
      while(insn.getPosition() < 74)
        insn = insn.getNext();
      sf.pop(); sf.pop();
      ((PCChoiceGenerator) ti.getVM().getSystemState().getChoiceGenerator()).setCurrentPC(pc);
      ti.setNextPC(insn);
    }
  }

  // produced by Soot
  public void VeritestingPerf_countBitsSet_VT_11_23_soot
          (VM vm, ThreadInfo ti, Instruction instructionToExecute) {
    if(ti.getTopFrame().getPC().getPosition() == 11 &&
            ti.getTopFrame().getMethodInfo().getName().equals("countBitsSet") &&
            ti.getTopFrame().getClassInfo().getName().equals("VeritestingPerf")) {
      StackFrame sf = ti.getTopFrame();
      BinaryLinearIntegerExpression lowbit = (BinaryLinearIntegerExpression) sf.getLocalAttr(3);
      SymbolicInteger flag_2 = makeSymbolicInteger("flag_2"+pathLabelCount);
      SymbolicInteger flag_1 = makeSymbolicInteger("flag_1"+pathLabelCount);
      SymbolicInteger flag_3 = makeSymbolicInteger("flag_3"+pathLabelCount);
      SymbolicInteger pathLabel0 = makeSymbolicInteger("pathLabel"+pathLabelCount);
      PathCondition pc;
      pc = ((PCChoiceGenerator) ti.getVM().getSystemState().getChoiceGenerator()).getCurrentPC();
      pc._addDet(new ComplexNonLinearIntegerConstraint(

              new ComplexNonLinearIntegerExpression(
                      new ComplexNonLinearIntegerExpression(
                              new ComplexNonLinearIntegerExpression(new ComplexNonLinearIntegerExpression(lowbit, EQ, new IntegerConstant(0)),
                                      LOGICAL_AND,
                                      new ComplexNonLinearIntegerExpression(
                                              new ComplexNonLinearIntegerExpression(flag_1, EQ, new IntegerConstant(0)),
                                              LOGICAL_AND,
                                              new ComplexNonLinearIntegerExpression(pathLabel0, EQ, new IntegerConstant(pathLabelCount)))),
                              LOGICAL_OR,
                              new ComplexNonLinearIntegerExpression(new ComplexNonLinearIntegerExpression(lowbit, NE, new IntegerConstant(0)),
                                      LOGICAL_AND,
                                      new ComplexNonLinearIntegerExpression(
                                              new ComplexNonLinearIntegerExpression(flag_2, EQ, new IntegerConstant(1)),
                                              LOGICAL_AND,
                                              new ComplexNonLinearIntegerExpression(pathLabel0, EQ, new IntegerConstant(pathLabelCount+1))))),
                      LOGICAL_AND,
                      new ComplexNonLinearIntegerExpression(
                              new ComplexNonLinearIntegerExpression(
                                      new ComplexNonLinearIntegerExpression(pathLabel0, EQ, new IntegerConstant(pathLabelCount)),
                                      LOGICAL_AND,
                                      new ComplexNonLinearIntegerExpression(flag_3, EQ, flag_1)),
                              LOGICAL_OR,
                              new ComplexNonLinearIntegerExpression(
                                      new ComplexNonLinearIntegerExpression(pathLabel0, EQ, new IntegerConstant(pathLabelCount+1)),
                                      LOGICAL_AND,
                                      new ComplexNonLinearIntegerExpression(flag_3, EQ, flag_2))))));
      sf.setSlotAttr(4, flag_3);
      Instruction insn=instructionToExecute;
      while(insn.getPosition() != 23) {
        if(insn instanceof GOTO)  insn = ((GOTO) insn).getTarget();
        else insn = insn.getNext();
      }    sf.pop();
      ((PCChoiceGenerator) ti.getVM().getSystemState().getChoiceGenerator()).setCurrentPC(pc);
      ti.setNextPC(insn);
      pathLabelCount+=5;
    }
  }

  public void VeritestingPerf_countBitsSet_VT_11_16
          (ThreadInfo ti, Instruction instructionToExecute) {
    if(ti.getTopFrame().getPC().getPosition() == 11 &&
            ti.getTopFrame().getMethodInfo().getName().equals("countBitsSet") &&
            ti.getTopFrame().getClassInfo().getName().equals("VeritestingPerf")) {
      StackFrame sf = ti.getTopFrame();
      InstructionInfo instructionInfo = new InstructionInfo(ti).invoke();
      Comparator trueComparator = instructionInfo.getTrueComparator();
      Comparator falseComparator = instructionInfo.getFalseComparator();
      int numOperands = instructionInfo.getNumOperands();
      ComplexNonLinearIntegerExpression condition = instructionInfo.getCondition();
      ComplexNonLinearIntegerExpression negCondition = instructionInfo.getNegCondition();
      if(condition == null || negCondition == null) return;
      PathCondition pc;
      pc = ((PCChoiceGenerator) ti.getVM().getSystemState().getChoiceGenerator()).getCurrentPC();
      PathCondition eqPC = pc.make_copy();
      PathCondition nePC = pc.make_copy();
      IntegerExpression sym_v = (IntegerExpression) sf.getOperandAttr();
      eqPC._addDet(trueComparator, sym_v, 0);
      nePC._addDet(falseComparator, sym_v, 0);
      boolean eqSat = eqPC.simplify();
      boolean neSat = nePC.simplify();
      if(!eqSat && !neSat) {
        System.out.println("both sides of branch at offset 11 are unsat");
        assert(false);
      }
      if( (eqSat && !neSat) || (!eqSat && neSat)) {
        return;
      }
      SymbolicInteger v7 = makeSymbolicInteger("v7" + pathLabelCount);
      SymbolicInteger pathLabel0 = makeSymbolicInteger("pathLabel0" + pathLabelCount);
      IntegerExpression cnlie =
              new ComplexNonLinearIntegerExpression(
                      new ComplexNonLinearIntegerExpression(
                              new ComplexNonLinearIntegerExpression(condition,
                                      LOGICAL_AND,
                                      new ComplexNonLinearIntegerExpression(pathLabel0, EQ, new IntegerConstant(1))),
                              LOGICAL_OR,
                              new ComplexNonLinearIntegerExpression(negCondition,
                                      LOGICAL_AND,
                                      new ComplexNonLinearIntegerExpression(pathLabel0, EQ, new IntegerConstant(2)))),
                      LOGICAL_AND,
                      new ComplexNonLinearIntegerExpression(
                              new ComplexNonLinearIntegerExpression(
                                      new ComplexNonLinearIntegerExpression(pathLabel0, EQ, new IntegerConstant(1)),
                                      LOGICAL_AND,
                                      new ComplexNonLinearIntegerExpression(v7, EQ, new IntegerConstant(0))),
                              LOGICAL_OR,
                              new ComplexNonLinearIntegerExpression(
                                      new ComplexNonLinearIntegerExpression(pathLabel0, EQ, new IntegerConstant(2)),
                                      LOGICAL_AND,
                                      new ComplexNonLinearIntegerExpression(v7, EQ, new IntegerConstant(1)))));
      cnlie = constantFold(cnlie);
      pc._addDet(new ComplexNonLinearIntegerConstraint((ComplexNonLinearIntegerExpression) cnlie));
      sf.setSlotAttr(3,  v7);

      Instruction insn=instructionToExecute;
      while(insn.getPosition() != 16) {
        if(insn instanceof GOTO)  insn = ((GOTO) insn).getTarget();
        else insn = insn.getNext();
      }
      while(numOperands > 0) { sf.pop(); numOperands--; }
      ((PCChoiceGenerator) ti.getVM().getSystemState().getChoiceGenerator()).setCurrentPC(pc);
      ti.setNextPC(insn);
      pathLabelCount+=1;
    }
  }

  public void VeritestingPerf_testMe4_VT_57_69
          (ThreadInfo ti, Instruction instructionToExecute) {
    if(ti.getTopFrame().getPC().getPosition() == 57 &&
            ti.getTopFrame().getMethodInfo().getName().equals("testMe4") &&
            ti.getTopFrame().getClassInfo().getName().equals("VeritestingPerf")) {
      StackFrame sf = ti.getTopFrame();
      InstructionInfo instructionInfo = new InstructionInfo(ti).invoke();
      Comparator trueComparator = instructionInfo.getTrueComparator();
      Comparator falseComparator = instructionInfo.getFalseComparator();
      int numOperands = instructionInfo.getNumOperands();
      ComplexNonLinearIntegerExpression condition = instructionInfo.getCondition();
      ComplexNonLinearIntegerExpression negCondition = instructionInfo.getNegCondition();
      if(condition == null || negCondition == null) return;
      PathCondition pc;
      pc = ((PCChoiceGenerator) ti.getVM().getSystemState().getChoiceGenerator()).getCurrentPC();
      PathCondition eqPC = pc.make_copy();
      PathCondition nePC = pc.make_copy();
      IntegerExpression sym_v = (IntegerExpression) sf.getOperandAttr();
      eqPC._addDet(trueComparator, sym_v, 0);
      nePC._addDet(falseComparator, sym_v, 0);
      boolean eqSat = eqPC.simplify();
      boolean neSat = nePC.simplify();
      if(!eqSat && !neSat) {
        System.out.println("both sides of branch at offset 11 are unsat");
        assert(false);
      }
      if( (eqSat && !neSat) || (!eqSat && neSat)) {
        return;
      }
      IntegerExpression v26 = (IntegerExpression) sf.getLocalAttr(3);
      if (v26 == null) {
        v26 = new IntegerConstant(sf.getLocalVariable(3));
      }
      IntegerExpression v22 = makeSymbolicInteger("v22" + pathLabelCount);
      IntegerExpression v23 = makeSymbolicInteger("v23" + pathLabelCount);
      IntegerExpression v24 = makeSymbolicInteger("v24" + pathLabelCount);
      IntegerExpression pathLabel0 = makeSymbolicInteger("pathLabel0" + pathLabelCount);
      IntegerExpression cnlie =
              new ComplexNonLinearIntegerExpression(
                      new ComplexNonLinearIntegerExpression(
                              new ComplexNonLinearIntegerExpression(condition,
                                      LOGICAL_AND,
                                      new ComplexNonLinearIntegerExpression(new ComplexNonLinearIntegerExpression(v23, EQ, new ComplexNonLinearIntegerExpression(v26, PLUS, new IntegerConstant(1)) ),
                                              LOGICAL_AND,
                                              new ComplexNonLinearIntegerExpression(pathLabel0, EQ, new IntegerConstant(3)))),
                              LOGICAL_OR,
                              new ComplexNonLinearIntegerExpression(negCondition,
                                      LOGICAL_AND,
                                      new ComplexNonLinearIntegerExpression(new ComplexNonLinearIntegerExpression(v22, EQ, new ComplexNonLinearIntegerExpression(v26, PLUS, new IntegerConstant(-1)) ),
                                              LOGICAL_AND,
                                              new ComplexNonLinearIntegerExpression(pathLabel0, EQ, new IntegerConstant(4))))),
                      LOGICAL_AND,
                      new ComplexNonLinearIntegerExpression(
                              new ComplexNonLinearIntegerExpression(
                                      new ComplexNonLinearIntegerExpression(pathLabel0, EQ, new IntegerConstant(3)),
                                      LOGICAL_AND,
                                      new ComplexNonLinearIntegerExpression(v24, EQ,  v23)),
                              LOGICAL_OR,
                              new ComplexNonLinearIntegerExpression(
                                      new ComplexNonLinearIntegerExpression(pathLabel0, EQ, new IntegerConstant(4)),
                                      LOGICAL_AND,
                                      new ComplexNonLinearIntegerExpression(v24, EQ, v22))));
      cnlie = constantFold(cnlie);
      pc._addDet(new ComplexNonLinearIntegerConstraint((ComplexNonLinearIntegerExpression) cnlie));
      sf.setSlotAttr(3,   v24);

      Instruction insn=instructionToExecute;
      while(insn.getPosition() != 69) {
        if(insn instanceof GOTO)  insn = ((GOTO) insn).getTarget();
        else insn = insn.getNext();
      }
      while(numOperands > 0) { sf.pop(); numOperands--; }
      ((PCChoiceGenerator) ti.getVM().getSystemState().getChoiceGenerator()).setCurrentPC(pc);
      ti.setNextPC(insn);
      pathLabelCount+=1;
    }
  }

  */
}
