/* Soot - a J*va Optimization Framework
 * Copyright (C) 2008 Eric Bodden
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the
 * Free Software Foundation, Inc., 59 Temple Place - Suite 330,
 * Boston, MA 02111-1307, USA.
 */
import java.util.Map;
import java.util.List;
import java.util.Iterator;
import java.util.HashSet;

import soot.Body;
import soot.Local;
import soot.SootMethod;
import soot.Unit;
import soot.util.Chain;
import soot.jimple.*;
import soot.shimple.*;
import soot.BodyTransformer;
import soot.G;
import soot.PackManager;
import soot.Transform;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.MHGPostDominatorsFinder;
import soot.tagkit.*;

public class MyMain {

  public static int pathLabelVarNum=0;
  public static HashSet endingInsnsHash;
  public static void main(String[] args) {
    endingInsnsHash = new HashSet();
    // this jb pack does not work, perhaps, by design
    PackManager.v().getPack("jb").add(
        new Transform("jb.myTransform", new BodyTransformer() {
          protected void internalTransform(Body body, String phase, Map options) {
            SootMethod method = body.getMethod();
            Chain units = body.getUnits();
            Iterator it = units.snapshotIterator();
            while(it.hasNext()) 
              G.v().out.println("*it = "+it.next());
          }
        }));
    PackManager.v().getPack("stp").add(
        new Transform("stp.myTransform", new BodyTransformer() {
          protected void internalTransform(Body body, String phase, Map options) {
            // // prints out locals, but those dont have stack locations
            // Chain<Local> locals = body.getLocals();
            // G.v().out.println("locals = "+locals);
            // Iterator it = locals.iterator();
            // while(it.hasNext()) {
            //   Local l = (Local) it.next();
            //   G.v().out.println("l.name = " + l.getName() + 
            //     " l.type = " + l.getType() + 
            //     " l.num = " + l.getNumber() + 
            //     " l.getUB = " + l.getUseBoxes());
            // }
            MyAnalysis m = new MyAnalysis(new ExceptionalUnitGraph(body));
            // use G.v().out instead of System.out so that Soot can
            // redirect this output to the Eclipse console
            // if(!body.getMethod().getName().contains("testMe3")) return;
            // G.v().out.println(body.getMethod());
            // Iterator it = body.getUnits().iterator();
            // while (it.hasNext()) {
            //   Unit u = (Unit) it.next();
            //   MyStmtSwitch myStmtSwitch = new MyStmtSwitch();
            //   u.apply(myStmtSwitch);
            //   //G.v().out.println(u);
            //   G.v().out.println("");
            // }
          } 
        } 
        )
    );
    soot.Main.main(args);
  }
  
  public static class MyAnalysis /*extends ForwardFlowAnalysis */ {
    ExceptionalUnitGraph g; 
    HashSet startingPointsHistory;
    LocalVarsTable lvt;
    String className, methodName;
    public MyAnalysis(ExceptionalUnitGraph exceptionalUnitGraph) {
      g = exceptionalUnitGraph;
      className = g.getBody().getMethod().getDeclaringClass().getName();
      methodName = g.getBody().getMethod().getName();
      lvt = new LocalVarsTable(className, methodName); 
      G.v().out.println("Starting analysis for "+g.getBody().getMethod().getName());
      List<Unit> heads = g.getHeads();
      startingPointsHistory = new HashSet();
      for(int i=0; i<heads.size(); i++) {
        Unit u = (Unit) heads.get(i);
        doAnalysis(u);
      }
    }
    
    private void printTags(Stmt stmt) {
      Iterator tags_it = stmt.getTags().iterator();
      while(tags_it.hasNext()) G.v().out.println(tags_it.next());
      G.v().out.println("  end tags");
    }
    
    public Unit getIPDom(Unit u) {
      MHGPostDominatorsFinder m = new MHGPostDominatorsFinder(g);
      Unit u_IPDom = (Unit) m.getImmediateDominator(u);
      return u_IPDom;
    }


    public void doAnalysis(Unit startingUnit) {
      G.v().out.println("Starting doAnalysis");
      Unit u = startingUnit;
      MyStmtSwitch myStmtSwitch;
      HashSet h = new HashSet();
      boolean isLoop = false;
      if(startingPointsHistory.contains(startingUnit)) return;
      while(true) {
        if(u == null) break;
        if(h.contains(u)) { isLoop = true; break; }
        else h.add(u);
        //printTags((Stmt)u);
        // G.v().out.println("BOTag = " + ((Stmt)u).getTag("BytecodeOffsetTag"));
        List<Unit> succs = g.getUnexceptionalSuccsOf(u);
        Unit commonSucc = getIPDom(u);
        if(succs.size()==1) {
          u = succs.get(0);
          continue;
        } else if (succs.size()==0) 
          break;
        else if(succs.size() == 2 && startingPointsHistory.contains(u)) {
            u = commonSucc;
            break;
        } else if(succs.size() == 2 && !startingPointsHistory.contains(u)) {
          startingPointsHistory.add(u);
          lvt.resetUsedLocalVars();
          lvt.resetIntermediateVars();
          // G.v().out.printf("  #succs = %d\n", succs.size());
          myStmtSwitch = new MyStmtSwitch(lvt);
          u.apply(myStmtSwitch);
          String if_SPFExpr = myStmtSwitch.getSPFExpr();
          String ifNot_SPFExpr = myStmtSwitch.getIfNotSPFExpr();
          Unit thenUnit = succs.get(1); //assuming this order for now
          Unit elseUnit = succs.get(0);
          String thenExpr="", elseExpr="";
          final int thenPathLabel = MyUtils.getPathCounter();
          final int elsePathLabel = MyUtils.getPathCounter();
          final String thenPLAssignSPF = 
            MyUtils.nCNLIE + "pathLabel" + pathLabelVarNum + ", EQ, new IntegerConstant(" + thenPathLabel + "))"; 
          final String elsePLAssignSPF = 
            MyUtils.nCNLIE + "pathLabel" + pathLabelVarNum + ", EQ, new IntegerConstant(" + elsePathLabel + "))";
          boolean canVeritest = true;

          // Create thenExpr
          while(thenUnit != commonSucc) {
            // G.v().out.println("BOTag = " + ((Stmt)thenUnit).getTag("BytecodeOffsetTag") + 
            //     ", h.size() = " + h.size());
            if(h.contains(thenUnit)) { 
              isLoop = true;
              List<Unit> thenSuccs;
              while(true) {
                thenSuccs = g.getUnexceptionalSuccsOf(thenUnit);
                if(thenSuccs.size() > 1) break; 
                thenUnit = thenSuccs.get(0);
              }
              // G.v().out.println(" calling doAnalysis on succ 0");
              doAnalysis(thenSuccs.get(0));
              // G.v().out.println(" calling doAnalysis on succ 1");
              doAnalysis(thenSuccs.get(1));
              break; 
            }
            else h.add(thenUnit);
            myStmtSwitch = new MyStmtSwitch(lvt);
            thenUnit.apply(myStmtSwitch);
            if(myStmtSwitch.getCanVeritest() == false) {
	      G.v().out.println("Stmt " + thenUnit + " cannot veritest");
              canVeritest = false;
              break;
            }
            String thenExpr1 = myStmtSwitch.getSPFExpr();
            if(thenExpr1 == null || thenExpr1 == "" ) {
              thenUnit = g.getUnexceptionalSuccsOf(thenUnit).get(0);
              continue;
            }
            if(thenExpr!="") 
              thenExpr = MyUtils.SPFLogicalAnd(thenExpr, thenExpr1);
            else thenExpr = thenExpr1;
            thenUnit = g.getUnexceptionalSuccsOf(thenUnit).get(0);
          }
          if(isLoop) {
            G.v().out.println("Found a loop");
	    canVeritest = false;
          }
          // Assign pathLabel a value in the thenExpr
          if(canVeritest) 
            thenExpr = MyUtils.SPFLogicalAnd(thenExpr, thenPLAssignSPF);

          h.clear();
          isLoop = false;
          while(canVeritest && (elseUnit != commonSucc)) {
            if(h.contains(elseUnit)) { 
              isLoop = true;
              List<Unit> elseSuccs;
              while(true) {
                elseSuccs = g.getUnexceptionalSuccsOf(elseUnit);
                if(elseSuccs.size() > 1) break; 
                elseUnit = elseSuccs.get(0);
              }
              doAnalysis(elseSuccs.get(0));
              doAnalysis(elseSuccs.get(1));
              break; 
            }
            else h.add(elseUnit);
            // G.v().out.println("BOTag = " + ((Stmt)elseUnit).getTag("BytecodeOffsetTag") + 
            //     ", h.size() = " + h.size());
            myStmtSwitch = new MyStmtSwitch(lvt);
            elseUnit.apply(myStmtSwitch);
            if(myStmtSwitch.getCanVeritest() == false) {
              canVeritest = false;
              break;
            }
            String elseExpr1 = myStmtSwitch.getSPFExpr();
            if(elseExpr1 == null || elseExpr1 == "" ) {
              elseUnit = g.getUnexceptionalSuccsOf(elseUnit).get(0);
              continue;
            }
            if(elseExpr!="") 
              elseExpr = MyUtils.SPFLogicalAnd(elseExpr, elseExpr1);
            else elseExpr = elseExpr1;
            elseUnit = g.getUnexceptionalSuccsOf(elseUnit).get(0);
          }
          if(isLoop) {
            G.v().out.println("Found an Else loop");
	    canVeritest = false;
          }
          // Assign pathLabel a value in the elseExpr
          if(canVeritest) {
            elseExpr = MyUtils.SPFLogicalAnd(elseExpr, elsePLAssignSPF);
          
	    // (If && thenExpr) || (ifNot && elseExpr)
	    String pathExpr1 = 
	      MyUtils.SPFLogicalOr( 
				   MyUtils.SPFLogicalAnd(if_SPFExpr, thenExpr),
				   MyUtils.SPFLogicalAnd(ifNot_SPFExpr, elseExpr));

	    final StringBuilder sB = new StringBuilder();
	    final StringBuilder setSlotAttr_SB = new StringBuilder();
	    final StringBuilder lhs_SB = new StringBuilder();
	    commonSucc.apply(new AbstractStmtSwitch() {
		public void caseAssignStmt(AssignStmt stmt) {
		  String lhs = stmt.getLeftOp().toString();
		  lhs_SB.append(lhs);
		  String s_tmp = new String("sf.setSlotAttr("+
					    lvt.getLocalVarSlot(lhs.substring(0,lhs.length()-2))+
					    ", " + lhs + ");");
		  setSlotAttr_SB.append(s_tmp);
		  MyShimpleValueSwitch msvs = new MyShimpleValueSwitch(lvt);
		  stmt.getRightOp().apply(msvs);
		  String phiExpr0 = msvs.getArg0PhiExpr();
		  String phiExpr1 = msvs.getArg1PhiExpr();

		  String phiExpr0_s = MyUtils.nCNLIE + lhs + ", EQ, " + phiExpr0 + ")";
		  String phiExpr1_s = MyUtils.nCNLIE + lhs + ", EQ, " + phiExpr1 + ")";
		  // (pathLabel == 1 && lhs == phiExpr0) || (pathLabel ==2 && lhs == phiExpr1)
		  sB.append( MyUtils.SPFLogicalOr(
						  MyUtils.SPFLogicalAnd( thenPLAssignSPF,
									 phiExpr0_s),
						  MyUtils.SPFLogicalAnd( elsePLAssignSPF,
									 phiExpr1_s
									 )));
		}});
	    String startingInsn = ((Stmt)u).getTag("BytecodeOffsetTag").toString();
	    String endingInsn;
	    while(true) {
	      Tag t = ((Stmt)commonSucc).getTag("BytecodeOffsetTag");
	      if(t == null) {
		commonSucc = g.getUnexceptionalSuccsOf(commonSucc).get(0);
		continue;
	      } else { 
		endingInsn = t.toString();
		int eiSetupInsn = lvt.getSetupInsn(Integer.parseInt(endingInsn));
		if(eiSetupInsn!= -1) {
		  endingInsn = Integer.toString(eiSetupInsn);
		}
		break;
	      }
	    }
	    String finalPathExpr = MyUtils.SPFLogicalAnd(pathExpr1, sB.toString());
	    // G.v().out.println("At offset = " + startingInsn + 
	    //     " finalPathExpr = "+finalPathExpr);
	    // G.v().out.println("lvt.usedLocalVars.size = " + lvt.usedLocalVars.size());
	    u = commonSucc;

	    // Generate the executeInstruction listener function
	    String fn = "public void " + className + 
	      "_" + methodName + "_VT_" + startingInsn + "_" + endingInsn + "\n";
	    fn += " (VM vm, ThreadInfo ti, Instruction instructionToExecute) {\n";
	    fn += "  if(ti.getTopFrame().getPC().getPosition() == " + startingInsn + " && \n";
	    fn += "     ti.getTopFrame().getMethodInfo().getName().equals(\"" + methodName + "\") && \n";
	    fn += "     ti.getTopFrame().getClassInfo().getName().equals(\"" + className + "\")) {\n";
	    fn += "    StackFrame sf = ti.getTopFrame();\n";
	    Iterator it = lvt.usedLocalVars.iterator();
	    while(it.hasNext()) {
	      String s = (String) it.next();
	      int slot = lvt.getLocalVarSlot(s);
	      if(slot!=-1) {
		fn += "    SymbolicInteger "+s+" = (SymbolicInteger) sf.getLocalAttr("+slot+");\n";
	      }
	    }
	    it = lvt.intermediateVars.iterator();
	    while(it.hasNext()) {
	      String s = (String) it.next();
	      fn += "    SymbolicInteger " + s + " = makeSymbolicInteger(ti.getEnv(), \"" + s + "\");\n";
	    }
	    fn += "    SymbolicInteger " + lhs_SB.toString() + " = makeSymbolicInteger(ti.getEnv(), \"" + lhs_SB.toString() + "\");\n";
	    fn += "    SymbolicInteger pathLabel" + pathLabelVarNum + " = makeSymbolicInteger(ti.getEnv(), \"pathLabel" + pathLabelVarNum+ "\");\n";
	    fn += "    PathCondition pc;\n";
	    fn += "    pc = ((PCChoiceGenerator) ti.getVM().getSystemState().getChoiceGenerator()).getCurrentPC();\n";
	    fn += "    pc._addDet(new ComplexNonLinearIntegerConstraint(\n    " + finalPathExpr + "));\n";
	    fn += "    " + setSlotAttr_SB.toString() + "\n";
	    fn += "    Instruction insn=instructionToExecute;\n";
	    fn += "    while(insn.getPosition() < " + endingInsn + ")\n";
	    fn += "      insn = insn.getNext();\n";
	    if(!endingInsnsHash.contains(startingInsn))
	      fn += "    sf.pop(); sf.pop();\n"; // popping the region's starting node (if stmt) operands
	    fn += "    ((PCChoiceGenerator) ti.getVM().getSystemState().getChoiceGenerator()).setCurrentPC(pc);\n";
	    fn += "    ti.setNextPC(insn);\n";
	    fn += "  }\n";
	    fn += "}\n";

	    G.v().out.println(fn);
	    endingInsnsHash.add(endingInsn);

	    lvt.resetUsedLocalVars();
	    lvt.resetIntermediateVars();
	    pathLabelVarNum++;
          } // end if(canVeritest) 
	  else { u = commonSucc; }
        } else {
          G.v().out.println("more than 2 successors unhandled");
        }
        G.v().out.println("");
      } // end while(true)
      if(u != null && u != startingUnit) doAnalysis(u);
      if(isLoop) {
        doAnalysis(g.getUnexceptionalSuccsOf(u).get(0));
        doAnalysis(g.getUnexceptionalSuccsOf(u).get(1));
      }
    } // end doAnalysis

  } // end MyAnalysis class
  
}
