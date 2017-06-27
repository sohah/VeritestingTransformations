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
import gov.nasa.jpf.vm.VM;
import gov.nasa.jpf.vm.ThreadInfo;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.PropertyListenerAdapter;
import gov.nasa.jpf.search.Search;
import gov.nasa.jpf.symbc.numeric.PCChoiceGenerator;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.BinaryNonLinearIntegerExpression;
import gov.nasa.jpf.vm.ChoiceGenerator;
import gov.nasa.jpf.vm.StackFrame;

import static gov.nasa.jpf.symbc.numeric.Operator.*;

public class VeritestingListener extends PropertyListenerAdapter  {
  
  public VeritestingListener(Config conf, JPF jpf) {
  }
  
  public void executeInstruction(VM vm, ThreadInfo currentThread, Instruction instructionToExecute) {
    int startInsn = 40, endInsn = 68;
    //System.out.println(currentThread.getTopFrame().getPC().getPosition()); 
    if(currentThread.getTopFrame().getPC().getPosition() == startInsn && 
       currentThread.getTopFrame().getMethodInfo().getName().equals("testMe3") &&
       currentThread.getTopFrame().getClassInfo().getName().equals("TestPaths")) { 
      StackFrame sf = currentThread.getTopFrame();
      System.out.println("time to start veritesting for " + 
       currentThread.getTopFrame().getMethodInfo().getName());
      System.out.println("topPos = "+sf.getTopPos());
      
      // Causes assert on StackFrame.java:576 to fail
      IntegerExpression x_v = (IntegerExpression) sf.getOperandAttr();
      if(x_v == null) System.out.println("failed to get x expr");
      
      int a_val = sf.getSlot(2);
      sf.setOperand(1, 0, false);
      sf.setSlotAttr(2, 
         new BinaryNonLinearIntegerExpression(new IntegerConstant(1), 
                PLUS, new IntegerConstant(a_val)));
      int b_val = sf.getSlot(3);
      sf.setOperand(0, 0, false);
      sf.setSlotAttr(3, 
         new BinaryNonLinearIntegerExpression(new IntegerConstant(1), 
                PLUS, new IntegerConstant(b_val)));
      
      Instruction insn=instructionToExecute;
      while(insn.getPosition() < endInsn) 
        insn = insn.getNext();
      currentThread.setNextPC(insn);
    }
  }
}
