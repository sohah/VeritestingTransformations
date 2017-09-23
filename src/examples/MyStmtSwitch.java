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
  String SPFExpr, ifNotSPFExpr;
  LocalVarsTable lvt;
  String getSPFExpr() { return SPFExpr; }
  String getIfNotSPFExpr() { return ifNotSPFExpr; }
  Boolean getCanVeritest() { return canVeritest; }

  public MyStmtSwitch(LocalVarsTable _lvt) { lvt = _lvt; }

  public void caseAssignStmt(AssignStmt stmt) {
    String rightStr = stmt.getRightOp().toString();

    if(MyUtils.isIntegerConstant(stmt.getRightOp()))
      rightStr = "new IntegerConstant(" + stmt.getRightOp().toString()+")";
    else { 
      MyShimpleValueSwitch msvw = new MyShimpleValueSwitch(lvt);
      stmt.getRightOp().apply(msvw);
      String s_tmp = msvw.getIfExprStr_SPF();
      if(s_tmp != null && s_tmp != "") { rightStr = s_tmp; }
    }
    SPFExpr = MyUtils.nCNLIE + 
      stmt.getLeftOp().toString() + ", EQ, " + rightStr + ")";
    lvt.addIntermediateVar(stmt.getLeftOp().toString());
    // G.v().out.println("  AssignStmt: "+stmt);
    canVeritest = true;
  }

  public void caseBreakpointStmt(BreakpointStmt stmt) {
    // G.v().out.println("  BreakpointStmt: "+stmt);
    canVeritest = false;
  }
  public void caseEnterMonitorStmt(EnterMonitorStmt stmt) {
    // G.v().out.println("  EnterMonitorStmt: "+stmt);
    canVeritest = false;
  }
  public void caseExitMonitorStmt(ExitMonitorStmt stmt) {
    // G.v().out.println("  ExitMonitorStmt: "+stmt);
    canVeritest = false;
  }
  public void caseGotoStmt(GotoStmt stmt) {
    // G.v().out.println("  GotoStmt: "+stmt);
    canVeritest = true;
  }
  public void caseIdentityStmt(IdentityStmt stmt) {
    // G.v().out.println("  IdentityStmt: "+stmt);
    canVeritest = false;
  }

  public void caseIfStmt(IfStmt stmt) {
    String if_SPFExpr, ifNot_SPFExpr, t_SPFExpr, tBody_SPFExpr;
    // G.v().out.println("  IfStmt: "+stmt);
    MyShimpleValueSwitch msvw = new MyShimpleValueSwitch(lvt);
    stmt.getCondition().apply(msvw);
    SPFExpr = msvw.getIfExprStr_SPF();
    ifNotSPFExpr = msvw.getIfNotExprStr_SPF();
    // Stmt t = stmt.getTarget();
    // MyStmtSwitch myStmtSwitch = new MyStmtSwitch();
    // t.apply(myStmtSwitch);
    // t_SPFExpr = myStmtSwitch.getSPFExpr();
    // tBody_SPFExpr = MyUtils.nCNLIE + if_SPFExpr + ", LOGICAL_AND, " + t_SPFExpr + ")";
    // G.v().out.printf("    IfStmt: if_SPFExpr = %s, ifNot_SPFExpr = %s\n", SPFExpr, ifNotSPFExpr);
    canVeritest = true;
  }

  public void caseInvokeStmt(InvokeStmt stmt) {
    // G.v().out.println("  InvokeStmt: "+stmt);
    canVeritest = false;
  }
  public void caseLookupSwitchStmt(LookupSwitchStmt stmt) {
    // G.v().out.println("  LookupSwitchStmt: "+stmt);
    canVeritest = false;
  }
  public void caseNopStmt(NopStmt stmt) {
    // G.v().out.println("  NopStmt: "+stmt);
    canVeritest = true;
  }
  public void caseRetStmt(RetStmt stmt) {
    // G.v().out.println("  RetStmt: "+stmt);
    canVeritest = false;
  }
  public void caseReturnStmt(ReturnStmt stmt) {
    // G.v().out.println("  ReturnStmt: "+stmt);
    canVeritest = false;
  }
  public void caseReturnVoidStmt(ReturnVoidStmt stmt) {
    // G.v().out.println("  ReturnVoidStmt: "+stmt);
    canVeritest = false;
  }
  public void caseTableSwitchStmt(TableSwitchStmt stmt) {
    // G.v().out.println("  TableSwitchStmt: "+stmt);
    canVeritest = false;
  }
  public void caseThrowStmt(ThrowStmt stmt) {
    // G.v().out.println("  ThrowStmt: "+stmt);
    canVeritest = false;
  }
  public void defaultCase(Object o) {
    // G.v().out.println("  defaultCase: "+o);
    canVeritest = false;
  }
}
