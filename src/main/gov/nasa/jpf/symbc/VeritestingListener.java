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
import gov.nasa.jpf.symbc.bytecode.ISHR;
import gov.nasa.jpf.symbc.numeric.*;
import gov.nasa.jpf.vm.*;

import static gov.nasa.jpf.symbc.numeric.Comparator.*;
import static gov.nasa.jpf.symbc.numeric.Operator.*;

public class VeritestingListener extends PropertyListenerAdapter  {

  int sumId=0;
  
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

  public SymbolicInteger makeSymbolicInteger(MJIEnv env, String name) {
    return new SymbolicInteger(name, MinMax.getVarMinInt(name), MinMax.getVarMaxInt(name));
  }

  // TestPathsSimple listener for testMe3
  public void executeInstruction_TestPathsSimple_testMe3(VM vm, ThreadInfo ti, Instruction instructionToExecute) {
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
      
      SymbolicInteger a_v = makeSymbolicInteger(ti.getEnv(),"a_final");
      SymbolicInteger b_v = makeSymbolicInteger(ti.getEnv(),"b_final");
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

  }

  // Veritesting listener for testMe4 method
  public void executeInstruction_VeritestingPerf_testMe4(VM vm, ThreadInfo ti, Instruction instructionToExecute) {
    int sum_slot_index = 3;
    int startInsn = 61, endInsn = 80; //TODO: read some of these from config 
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

      SymbolicInteger sum_new = makeSymbolicInteger(ti.getEnv(),"sum_new"+sumId);
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
  }

  // TestPaths listener
  public void executeInstruction_TestPaths(VM vm, ThreadInfo ti, Instruction instructionToExecute) {
    int x_slot_index = 1, y_slot_index = 2;
    //int a_final_slot_index = 3, b_final_slot_index = 4;
    int a_slot_index = 3, b_slot_index = 4;
    int startInsn = 7, endInsn = 46; //TODO: read some of these from config 
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
      SymbolicInteger a_v = makeSymbolicInteger(ti.getEnv(),"a_final");
      SymbolicInteger b_v = makeSymbolicInteger(ti.getEnv(),"b_final");
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

  public void executeInstruction(VM vm, ThreadInfo ti, Instruction instructionToExecute) {
    if(ti.getTopFrame().getPC().getPosition() == 46 && 
       ti.getTopFrame().getMethodInfo().getName().equals("testMe3") &&
       ti.getTopFrame().getClassInfo().getName().equals("TestPathsSimple")) {
      TestPathsSimple_testMe3_VT_46_58(vm, ti, instructionToExecute);
    } 
    else if(ti.getTopFrame().getPC().getPosition() == 62 && 
       ti.getTopFrame().getMethodInfo().getName().equals("testMe3") &&
       ti.getTopFrame().getClassInfo().getName().equals("TestPathsSimple")) {
      TestPathsSimple_testMe3_VT_62_74(vm, ti, instructionToExecute);
    }
    else if(ti.getTopFrame().getPC().getPosition() == 11 &&
            ti.getTopFrame().getMethodInfo().getName().equals("countBitsSet") &&
            ti.getTopFrame().getClassInfo().getName().equals("VeritestingPerf")) {
      VeritestingPerf_countBitsSet_VT_11_27(vm, ti, instructionToExecute);
    }
  }

public void TestPathsSimple_testMe3_VT_46_58
 (VM vm, ThreadInfo ti, Instruction instructionToExecute) {
  if(ti.getTopFrame().getPC().getPosition() == 46 && 
     ti.getTopFrame().getMethodInfo().getName().equals("testMe3") && 
     ti.getTopFrame().getClassInfo().getName().equals("TestPathsSimple")) {
    StackFrame sf = ti.getTopFrame();
    SymbolicInteger x = (SymbolicInteger) sf.getLocalAttr(1);
    SymbolicInteger a_2 = makeSymbolicInteger(ti.getEnv(), "a_2");
    SymbolicInteger a_1 = makeSymbolicInteger(ti.getEnv(), "a_1");
    SymbolicInteger a_3 = makeSymbolicInteger(ti.getEnv(), "a_3");
    SymbolicInteger pathLabel0 = makeSymbolicInteger(ti.getEnv(), "pathLabel0");
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
      SymbolicInteger b_1 = makeSymbolicInteger(ti.getEnv(), "b_1");
      SymbolicInteger b_2 = makeSymbolicInteger(ti.getEnv(), "b_2");
      SymbolicInteger b_3 = makeSymbolicInteger(ti.getEnv(), "b_3");
      SymbolicInteger pathLabel1 = makeSymbolicInteger(ti.getEnv(), "pathLabel1");
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

  public static int pathLabelCount = 1;

  public void VeritestingPerf_countBitsSet_VT_11_27
          (VM vm, ThreadInfo ti, Instruction instructionToExecute) {
    if(ti.getTopFrame().getPC().getPosition() == 11 &&
            ti.getTopFrame().getMethodInfo().getName().equals("countBitsSet") &&
            ti.getTopFrame().getClassInfo().getName().equals("VeritestingPerf")) {
      StackFrame sf = ti.getTopFrame();
      BinaryLinearIntegerExpression lowbit = (BinaryLinearIntegerExpression) sf.getLocalAttr(3);
      SymbolicInteger flag_2 = makeSymbolicInteger(ti.getEnv(), "flag_2"+pathLabelCount);
      SymbolicInteger flag_1 = makeSymbolicInteger(ti.getEnv(), "flag_1"+pathLabelCount);
      SymbolicInteger flag_3 = makeSymbolicInteger(ti.getEnv(), "flag_3"+pathLabelCount);
      SymbolicInteger pathLabel0 = makeSymbolicInteger(ti.getEnv(), "pathLabel"+pathLabelCount);
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
      pathLabelCount+=2;
    }
  }





}
