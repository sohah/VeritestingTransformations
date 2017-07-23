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
import soot.Type;
import soot.Value;

class MyStmtSwitch extends AbstractStmtSwitch {
	Boolean canVeritest;
	String SPFExpr;
	String nCNLIC = "new ComplexNonLinearIntegerConstraint(";

	String getSPFExpr() { return SPFExpr; }
	Boolean isVeritest() { return canVeritest; }

  public void caseAssignStmt(AssignStmt stmt) {
		String rightStr = stmt.getRightOp().toString();
		if(MyUtils.isIntegerConstant(stmt.getRightOp()))
			rightStr = "new IntegerConstant(" + stmt.getRightOp().toString()+")";
		SPFExpr = nCNLIC + stmt.getLeftOp().toString() + ", EQ, " + rightStr;
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
		String if_SPFExpr, notIf_SPFExpr, t_SPFExpr, tBody_SPFExpr;
    G.v().out.println("  IfStmt: "+stmt);
    MyShimpleValueSwitch msvw = new MyShimpleValueSwitch();
    stmt.getCondition().apply(msvw);
    if_SPFExpr = msvw.getIfExprStr_SPF();
    notIf_SPFExpr = msvw.getNotIfExprStr_SPF();
		Stmt t = stmt.getTarget();
		MyStmtSwitch myStmtSwitch = new MyStmtSwitch();
		t.apply(myStmtSwitch);
		t_SPFExpr = myStmtSwitch.getSPFExpr();
		tBody_SPFExpr = nCNLIC + if_SPFExpr + ", LOGICAL_AND, " + t_SPFExpr + ")";
    G.v().out.printf("    IfStmt: tBody = %s\n", 
		     tBody_SPFExpr);
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
