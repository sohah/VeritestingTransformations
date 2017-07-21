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

          protected void internalTransform(Body body, String phase, Map options) {
            new MyAnalysis(new ExceptionalUnitGraph(body));
            // use G.v().out instead of System.out so that Soot can
            // redirect this output to the Eclipse console
            G.v().out.println(body.getMethod());
            Iterator it = body.getUnits().iterator();
            while (it.hasNext()) {
              Unit u = (Unit) it.next();
              u.apply(new AbstractShimpleValueSwitch() {
		            public void caseEqExpr(EqExpr expr) {
		              //add(Baf.v().newIfEqInst(Baf.v().newPlaceholderInst(getTarget())));
                  G.v().out.println("EqExpr = "+expr);
		            }
		            public void caseNeExpr(NeExpr expr) {
		              //add(Baf.v().newIfNeInst(Baf.v().newPlaceholderInst(getTarget())));
                  G.v().out.println("NeExpr = "+expr);
		            }
		            public void caseLtExpr(LtExpr expr) {
		              //add(Baf.v().newIfLtInst(Baf.v().newPlaceholderInst(getTarget())));
                  G.v().out.println("LtExpr = "+expr);
		            }
		            public void caseLeExpr(LeExpr expr) {
		              //add(Baf.v().newIfLeInst(Baf.v().newPlaceholderInst(getTarget())));
                  G.v().out.println("LeExpr = "+expr);
		            }
		            public void caseGtExpr(GtExpr expr) {
		              //add(Baf.v().newIfGtInst(Baf.v().newPlaceholderInst(getTarget())));
                  G.v().out.println("GtExpr = "+expr);
		            }
		            public void caseGeExpr(GeExpr expr) {
		              //add(Baf.v().newIfGeInst(Baf.v().newPlaceholderInst(getTarget())));
                  G.v().out.println("GeExpr = "+expr);
		            }
		          }
		          );
              G.v().out.println(u);
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
