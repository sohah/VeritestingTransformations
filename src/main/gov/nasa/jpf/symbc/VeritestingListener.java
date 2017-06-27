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
import gov.nasa.jpf.symbc.numeric.Expression;
import gov.nasa.jpf.vm.ChoiceGenerator;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.MethodInfo;
import gov.nasa.jpf.vm.LocalVarInfo;

import static gov.nasa.jpf.symbc.numeric.Operator.*;

public class VeritestingListener extends PropertyListenerAdapter  {
  
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
 
  public void executeInstruction(VM vm, ThreadInfo currentThread, Instruction instructionToExecute) {
    int a_slot_index = 2, b_slot_index = 3;
    int startInsn = 40, endInsn = 68; //TODO: read these 4 things from config 
    if(currentThread.getTopFrame().getPC().getPosition() == startInsn && 
       currentThread.getTopFrame().getMethodInfo().getName().equals("testMe3") &&
       currentThread.getTopFrame().getClassInfo().getName().equals("TestPaths")) { 
      StackFrame sf = currentThread.getTopFrame();
      System.out.println("time to start veritesting for " + 
       currentThread.getTopFrame().getMethodInfo().getName());
      System.out.println("topPos = "+sf.getTopPos());
      
      IntegerExpression x_v = (IntegerExpression) sf.getLocalAttr(0);
      if(x_v == null) System.out.println("failed to get x expr");
      IntegerExpression y_v = (IntegerExpression) sf.getLocalAttr(0);
      if(y_v == null) System.out.println("failed to get y expr");
      
      int a_val = sf.getSlot(a_slot_index);
      sf.setSlotAttr(a_slot_index, 
         new BinaryNonLinearIntegerExpression(x_v, 
                PLUS, new IntegerConstant(a_val)));

      int b_val = sf.getSlot(b_slot_index);
      sf.setSlotAttr(b_slot_index, 
         new BinaryNonLinearIntegerExpression(y_v, 
                PLUS, new IntegerConstant(b_val)));
      
      Instruction insn=instructionToExecute;
      while(insn.getPosition() < endInsn) 
        insn = insn.getNext();
      currentThread.setNextPC(insn);
    }
  }
}
