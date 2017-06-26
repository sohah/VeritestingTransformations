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
    //System.out.println(currentThread.getTopFrame().getPC().getPosition()); 
    if(currentThread.getTopFrame().getPC().getPosition() == 38 && 
       currentThread.getTopFrame().getMethodInfo().getName().equals("testMe3") &&
       currentThread.getTopFrame().getClassInfo().getName().equals("TestPaths")) { 
      System.out.println("time to start veritesting for " + 
       currentThread.getTopFrame().getMethodInfo().getName());
      StackFrame sf = currentThread.getTopFrame();
      
      int offset=-1;
      System.out.println("topPos = "+sf.getTopPos());
      IntegerExpression sym_v = (IntegerExpression) sf.getOperandAttr(offset);
      if(sym_v == null) {
        int a_val = sf.getSlot(2);
        System.out.println("offset("+offset+") is concrete with value = "+a_val);
        sf.setOperandAttr(-1, 
              new BinaryNonLinearIntegerExpression(new IntegerConstant(a_val), 
                  PLUS, new IntegerConstant(1)));
      } else {
        System.out.println("offset("+offset+") is symbolic");
      }
      offset = -2;
      sym_v = (IntegerExpression) sf.getOperandAttr(offset);
      if(sym_v == null) {
        int a_val = sf.getSlot(3);
        System.out.println("offset("+offset+") is concrete with value = "+a_val);
        sf.setOperandAttr(-1, 
              new BinaryNonLinearIntegerExpression(new IntegerConstant(a_val), 
                  PLUS, new IntegerConstant(1)));
      } else {
        System.out.println("offset("+offset+") is symbolic");
      }
      
      Instruction insn=instructionToExecute;
      while(insn.getPosition() < 66) 
        insn = insn.getNext();
      currentThread.setNextPC(insn);
    }
  }
}
