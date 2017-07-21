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
            new MyAnalysis(new ExceptionalUnitGraph(body));
            // use G.v().out instead of System.out so that Soot can
            // redirect this output to the Eclipse console
            if(!body.getMethod().getName().contains("testMe3")) return;
            G.v().out.println(body.getMethod());
            Iterator it = body.getUnits().iterator();
            while (it.hasNext()) {
              Unit u = (Unit) it.next();
              u.apply(new AbstractStmtSwitch() {
		            public void caseAssignStmt(AssignStmt stmt) {
                  G.v().out.println("  AssignStmt: "+stmt);
		            }
		            public void caseBreakpointStmt(BreakpointStmt stmt) {
                  G.v().out.println("  BreakpointStmt: "+stmt);
		            }
		            public void caseEnterMonitorStmt(EnterMonitorStmt stmt) {
                  G.v().out.println("  EnterMonitorStmt: "+stmt);
		            }
		            public void caseExitMonitorStmt(ExitMonitorStmt stmt) {
                  G.v().out.println("  ExitMonitorStmt: "+stmt);
		            }
		            public void caseGotoStmt(GotoStmt stmt) {
                  G.v().out.println("  GotoStmt: "+stmt);
		            }
		            public void caseIdentityStmt(IdentityStmt stmt) {
                  G.v().out.println("  IdentityStmt: "+stmt);
		            }
		            public void caseIfStmt(IfStmt stmt) {
                  StringBuffer s;
                  stmt.toString(s);
                  G.v().out.println("  IfStmt: "+s);
		            }
		            public void caseInvokeStmt(InvokeStmt stmt) {
                  G.v().out.println("  InvokeStmt: "+stmt);
		            }
                public void caseLookupSwitchStmt(LookupSwitchStmt stmt) {
                  G.v().out.println("  LookupSwitchStmt: "+stmt);
		            }
                public void caseNopStmt(NopStmt stmt) {
                  G.v().out.println("  NopStmt: "+stmt);
		            }
                public void caseRetStmt(RetStmt stmt) {
                  G.v().out.println("  RetStmt: "+stmt);
		            }
                public void caseReturnStmt(ReturnStmt stmt) {
                  G.v().out.println("  ReturnStmt: "+stmt);
		            }
                public void caseReturnVoidStmt(ReturnVoidStmt stmt) {
                  G.v().out.println("  ReturnVoidStmt: "+stmt);
		            }
                public void caseTableSwitchStmt(TableSwitchStmt stmt) {
                  G.v().out.println("  TableSwitchStmt: "+stmt);
		            }
                public void caseThrowStmt(ThrowStmt stmt) {
                  G.v().out.println("  ThrowStmt: "+stmt);
		            }
                public void defaultCase(Object o) {
                  G.v().out.println("  defaultCase: "+o);
		            }
		          }
		          );
              //G.v().out.println(u);
              G.v().out.println("");
	          }
	        } 
	      } 
	      )
		);
    soot.Main.main(args);
  }
  
  public static class MyAnalysis /*extends ForwardFlowAnalysis */ {
    
    public MyAnalysis(ExceptionalUnitGraph exceptionalUnitGraph) {
      //doAnalysis();
    }

  }
  
}
