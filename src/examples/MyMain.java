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
import soot.Unit;
import soot.jimple.*;
import soot.shimple.*;
import soot.BodyTransformer;
import soot.G;
import soot.PackManager;
import soot.Transform;
import soot.toolkits.graph.ExceptionalUnitGraph;

public class MyMain {

  public static void main(String[] args) {
    PackManager.v().getPack("stp").add(
        new Transform("stp.myTransform", new BodyTransformer() {

          private void printTags(Stmt stmt) {
            Iterator tags_it = stmt.getTags().iterator();
            while(tags_it.hasNext()) G.v().out.println(tags_it.next());
            G.v().out.println("  end tags");
          }

          protected void internalTransform(Body body, String phase, Map options) {
            MyAnalysis m = new MyAnalysis(new ExceptionalUnitGraph(body));
            m.doAnalysis();
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

    public void doAnalysis() {
      List<Unit> heads = g.getHeads(); 
      if(heads.size()==1) {
        Unit u = (Unit) heads.get(0);
        MyStmtSwitch myStmtSwitch;
        while(true) {
          myStmtSwitch = new MyStmtSwitch();
          u.apply(myStmtSwitch);
          List<Unit> succs = g.getUnexceptionalSuccsOf(u);
          if(succs.size()==1) {
            u = succs.get(0);
            continue;
          } else if (succs.size()==0) break;
          else {
            G.v().out.printf("  #succs = %d\n", succs.size());
            String if_SPFExpr = myStmtSwitch.getIfSPFExpr();
            String ifNot_SPFExpr = myStmtSwitch.getIfNotSPFExpr();
            Unit commonSucc = getCommonSucc(succ); //TODO
            Unit thenUnit = succs.get(0);
            Unit elseUnit = succs.get(1);
            String thenExpr="", elseExpr="";
            int thenPathLabel = MyUtils.getPathCounter();
            int elsePathLabel = MyUtils.getPathCounter();
            while(thenUnit != commonSucc) {
              thenUnit.apply(myStmtSwitch);
              String thenExpr1 = myStmtSwitch.getSPFExpr();
              thenExpr = SPFLogicalAnd(thenExpr, thenExpr1); // TODO
              thenUnit = g.getUnexceptionalSuccsOf(thenUnit).get(0);
              thenExpr = SPFLogicalAnd(thenExpr, 
                   MyUtils.nCNLIC + "pathLabel, EQ, " + thenPathLabel + ")");
            }
            while(elseUnit != commonSucc) {
              elseUnit.apply(myStmtSwitch);
              String elseExpr1 = myStmtSwitch.getSPFExpr();
              elseExpr = SPFLogicalAnd(elseExpr, elseExpr1);
              elseUnit = g.getUnexceptionalSuccsOf(elseUnit).get(0);
              elseExpr = SPFLogicalAnd(elseExpr, 
                   MyUtils.nCNLIE + "pathLabel, EQ, " + elsePathLabel + ")");
            }
            String pathExpr1 = SPFLogicalOR( // TODO
                  SPFLogicalAnd(if_SPFExpr, thenExpr),
                  SPFLogicalAnd(ifNot_SPFExpr, elseExpr));
            final StringBuilder sB = new StringBuilder();
            commonSucc.apply(new AbstractStmtSwitch() {
              public void caseAssignStmt(AssignStmt stmt) {
                String lhs = stmt.getLeftOp().toString();
                MyShimpleValueSwitch msvs = new MyShimpleValueSwitch();
                stmt.apply(msvs);
                String phiExpr0 = msvs.getArg0PhiExpr();
                String phiExpr1 = msvs.getArg1PhiExpr();
                sB.append( SPFLogicalOR(
                  SPFLogicalAnd(
                    MyUtils.nCNLIE + "pathLabel, EQ, " + thenPathLabel + ")",
                    MyUtils.nCNLIE + lhs + ", EQ, " + phiExpr0), 
                  SPFLogicalAnd(
                    MyUtils.nCNLIE + "pathLabel, EQ, " + elsePathLabel + ")",
                    MyUtils.nCNLIE + lhs + ", EQ, " + phiExpr1)));
              }
            });
            String finalPathExpr = SPFLogicalAnd(pathExpr1, sB.toString());
          }
          G.v().out.println("");
        }
      }
    }

  }
  
}
