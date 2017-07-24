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

    public Unit getCommonSucc(List<Unit> units) {
      Unit u0 = units.get(0);
      Unit u1 = units.get(1);
      Unit u0_succ = u0;
      int cnt=0;
      while(cnt<MyUtils.maxSuccSteps) {
        u0_succ = g.getUnexceptionalSuccsOf(u0_succ).get(0);
        if(g.getPredsOf(u0_succ).size() > 1) {
          int cnt1=0;
          Unit u1_succ = u1;
          while(cnt1 < MyUtils.maxSuccSteps) {
            u1_succ = g.getUnexceptionalSuccsOf(u1_succ).get(0);
            if(g.getPredsOf(u1_succ).size() > 1 && u1_succ == u0_succ) {
              G.v().out.println("found common succ = "+u0_succ);
              return u0_succ;
            }
            cnt1++;
          }
        }
        cnt++;
      }
      return null;
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
            String if_SPFExpr = myStmtSwitch.getSPFExpr();
            String ifNot_SPFExpr = myStmtSwitch.getIfNotSPFExpr();
            Unit commonSucc = getCommonSucc(succs);
            Unit thenUnit = succs.get(0);
            Unit elseUnit = succs.get(1);
            String thenExpr="", elseExpr="";
            final int thenPathLabel = MyUtils.getPathCounter();
            final int elsePathLabel = MyUtils.getPathCounter();
            while(thenUnit != commonSucc) {
              thenUnit.apply(myStmtSwitch);
              String thenExpr1 = myStmtSwitch.getSPFExpr();
              if(thenExpr!="") 
                thenExpr = MyUtils.SPFLogicalAnd(thenExpr, thenExpr1);
              else thenExpr = thenExpr1;
              thenUnit = g.getUnexceptionalSuccsOf(thenUnit).get(0);
              thenExpr = MyUtils.SPFLogicalAnd(thenExpr, 
                   MyUtils.nCNLIE + "pathLabel, EQ, " + thenPathLabel + ")");
            }
            while(elseUnit != commonSucc) {
              elseUnit.apply(myStmtSwitch);
              String elseExpr1 = myStmtSwitch.getSPFExpr();
              if(elseExpr != "") 
                elseExpr = MyUtils.SPFLogicalAnd(elseExpr, elseExpr1);
              else elseExpr = elseExpr1;
              elseUnit = g.getUnexceptionalSuccsOf(elseUnit).get(0);
              elseExpr = MyUtils.SPFLogicalAnd(elseExpr, 
                   MyUtils.nCNLIE + "pathLabel, EQ, " + elsePathLabel + ")");
            }
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
                sB.append( MyUtils.SPFLogicalOr(
                  MyUtils.SPFLogicalAnd(
                    MyUtils.nCNLIE + "pathLabel, EQ, " + thenPathLabel + ")",
                    MyUtils.nCNLIE + lhs + ", EQ, " + phiExpr0), 
                  MyUtils.SPFLogicalAnd(
                    MyUtils.nCNLIE + "pathLabel, EQ, " + elsePathLabel + ")",
                    MyUtils.nCNLIE + lhs + ", EQ, " + phiExpr1)));
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
