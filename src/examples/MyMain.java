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

import soot.Body;
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

public class MyMain {

  public static void main(String[] args) {
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
    public MyAnalysis(ExceptionalUnitGraph exceptionalUnitGraph) {
      g = exceptionalUnitGraph;
      doAnalysis();
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

    public void doAnalysis() {
      List<Unit> heads = g.getHeads(); 
      if(heads.size()==1) {
        Unit u = (Unit) heads.get(0);
        MyStmtSwitch myStmtSwitch;
        while(true) {
          //printTags((Stmt)u);
          G.v().out.println("BytecodeOffsetTag = " + ((Stmt)u).getTag("BytecodeOffsetTag"));
          myStmtSwitch = new MyStmtSwitch();
          u.apply(myStmtSwitch);
          List<Unit> succs = g.getUnexceptionalSuccsOf(u);
          if(succs.size()==1) {
            u = succs.get(0);
            continue;
          } else if (succs.size()==0) break;
          else {
            G.v().out.printf("  #succs = %d\n", succs.size());
            String if_SPFExpr = myStmtSwitch.getSPFExpr();
            String ifNot_SPFExpr = myStmtSwitch.getIfNotSPFExpr();
            Unit commonSucc = getIPDom(u);
            Unit thenUnit = succs.get(0);
            Unit elseUnit = succs.get(1);
            String thenExpr="", elseExpr="";
            final int thenPathLabel = MyUtils.getPathCounter();
            final int elsePathLabel = MyUtils.getPathCounter();
            final String thenPLAssignSPF = 
              MyUtils.nCNLIE + "pathLabel, EQ, " + thenPathLabel + ")"; 
            final String elsePLAssignSPF = 
              MyUtils.nCNLIE + "pathLabel, EQ, " + elsePathLabel + ")";

            // Create thenExpr
            while(thenUnit != commonSucc) {
              myStmtSwitch = new MyStmtSwitch();
              thenUnit.apply(myStmtSwitch);
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
            // Assign pathLabel a value in the thenExpr
            thenExpr = MyUtils.SPFLogicalAnd(thenExpr, thenPLAssignSPF);

            // Create elseExpr, similar to thenExpr
            while(elseUnit != commonSucc) {
              myStmtSwitch = new MyStmtSwitch();
              elseUnit.apply(myStmtSwitch);
              String elseExpr1 = myStmtSwitch.getSPFExpr();
              if(elseExpr1 == null || elseExpr1 == "") {
                elseUnit = g.getUnexceptionalSuccsOf(elseUnit).get(0);
                continue;
              }
              if(elseExpr != "") 
                elseExpr = MyUtils.SPFLogicalAnd(elseExpr, elseExpr1);
              else elseExpr = elseExpr1;
              elseUnit = g.getUnexceptionalSuccsOf(elseUnit).get(0);
            }
            // Assign pathLabel a different value in the elseExpr
            elseExpr = MyUtils.SPFLogicalAnd(elseExpr, elsePLAssignSPF);

            // (If && thenExpr) || (ifNot && elseExpr)
            String pathExpr1 = MyUtils.SPFLogicalOr( 
                  MyUtils.SPFLogicalAnd(if_SPFExpr, thenExpr),
                  MyUtils.SPFLogicalAnd(ifNot_SPFExpr, elseExpr));

            final StringBuilder sB = new StringBuilder();
            commonSucc.apply(new AbstractStmtSwitch() {
              public void caseAssignStmt(AssignStmt stmt) {
                String lhs = stmt.getLeftOp().toString();
                MyShimpleValueSwitch msvs = new MyShimpleValueSwitch();
                stmt.getRightOp().apply(msvs);
                String phiExpr0 = msvs.getArg0PhiExpr();
                String phiExpr1 = msvs.getArg1PhiExpr();

                // (pathLabel == 1 && lhs == phiExpr0) || (pathLabel ==2 && lhs == phiExpr1)
                sB.append( MyUtils.SPFLogicalOr(
                  MyUtils.SPFLogicalAnd( thenPLAssignSPF,
                    MyUtils.nCNLIE + lhs + ", EQ, " + phiExpr0 + ")"), 
                  MyUtils.SPFLogicalAnd( elsePLAssignSPF, 
                    MyUtils.nCNLIE + lhs + ", EQ, " + phiExpr1 + ")")));
              }
            });
            String finalPathExpr = MyUtils.SPFLogicalAnd(pathExpr1, sB.toString());
            G.v().out.println("finalPathExpr = "+finalPathExpr);
            succs = g.getUnexceptionalSuccsOf(commonSucc);
            u = succs.get(0);
          }
          G.v().out.println("");
        }
      }
    }

  }
  
}
