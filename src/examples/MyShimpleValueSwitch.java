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
import soot.Type;
import soot.Value;
import soot.ValueBox;
import soot.toolkits.scalar.*;

class MyShimpleValueSwitch extends AbstractShimpleValueSwitch {
  String op1_str, op2_str, op;
  Type ty1, ty2;
  String ifExprStr_SPF, ifNotExprStr_SPF;
  String arg0PhiExpr, arg1PhiExpr;
  LocalVarsTable lvt; 

  public MyShimpleValueSwitch(LocalVarsTable _lvt) { lvt = _lvt; }

  String getArg0PhiExpr() { return arg0PhiExpr; }

  String getArg1PhiExpr() { return arg1PhiExpr; }

  String getIfExprStr_SPF() { return ifExprStr_SPF; }
	
  String getIfNotExprStr_SPF() { return ifNotExprStr_SPF; }

  void setupSPFExpr(BinopExpr v) {
    if(v.getOp1().getType().toString() == "int" && MyUtils.isIntegerConstant(v.getOp1()))
      op1_str = "new IntegerConstant(" + v.getOp1().toString() + ")";
    else op1_str = v.getOp1().toString();
    if(v.getOp2().getType().toString() == "int" && MyUtils.isIntegerConstant(v.getOp2()))
      op2_str = "new IntegerConstant(" + v.getOp2().toString() + ")";
    else op2_str = v.getOp2().toString();
    ty1 = v.getOp1().getType();
    ty2 = v.getOp2().getType();
    op = v.getSymbol();
  }

  public void caseAddExpr(AddExpr v) {
    setupSPFExpr(v);
    if( lvt.isLocalVariable(op1_str) ) {
      lvt.addUsedLocalVar(op1_str);
    }
    if( lvt.isLocalVariable(op2_str) ) {
      lvt.addUsedLocalVar(op2_str);
    }
    ifExprStr_SPF = "new ComplexNonLinearIntegerExpression(" + 
      op1_str + ", PLUS, " + op2_str + ")"; 
    ifNotExprStr_SPF = null; 
  }

  public void caseGtExpr(GtExpr v) {
    setupSPFExpr(v);
    if( lvt.isLocalVariable(op1_str) ) {
      lvt.addUsedLocalVar(op1_str);
      // G.v().out.println("added usedLocalVar = " + op1_str);
    }
    ifExprStr_SPF = "new ComplexNonLinearIntegerExpression(" + 
      op1_str + ", GT, " + op2_str + ")"; 
    ifNotExprStr_SPF = "new ComplexNonLinearIntegerExpression(" + 
      op1_str + ", LE, " + op2_str + ")"; 
    // G.v().out.println("    IfStmt(gt): v = "+v.getOp1()+"("+ty1+")" + " " + v.getOp2()+"("+ty2+")");
    // List<ValueBox> u = v.getUseBoxes();
    // G.v().out.println("    useboxes = "+u.get(0) + " " + u.get(1));
  }
  
  public void caseEqExpr(EqExpr v) {
    // G.v().out.println("    IfStmt(eq): v = "+v);
    setupSPFExpr(v);
    if( lvt.isLocalVariable(op1_str) ) {
      lvt.addUsedLocalVar(op1_str);
      // G.v().out.println("added usedLocalVar = " + op1_str);
    }
    ifExprStr_SPF = "new ComplexNonLinearIntegerExpression(" + 
      op1_str + ", EQ, " + op2_str + ")"; 
    ifNotExprStr_SPF = "new ComplexNonLinearIntegerExpression(" + 
      op1_str + ", NE, " + op2_str + ")"; 
  }
  
  public void caseGeExpr(GeExpr v) {
    // G.v().out.println("    IfStmt(ge): v = "+v);
    setupSPFExpr(v);
    if( lvt.isLocalVariable(op1_str) ) {
      lvt.addUsedLocalVar(op1_str);
      // G.v().out.println("added usedLocalVar = " + op1_str);
    }
    ifExprStr_SPF = "new ComplexNonLinearIntegerExpression(" + 
      op1_str + ", GE, " + op2_str + ")"; 
    ifNotExprStr_SPF = "new ComplexNonLinearIntegerExpression(" + 
      op1_str + ", LT, " + op2_str + ")"; 
    // G.v().out.println("    IfStmt(ge): v = 
    // "+v.getOp1()+"("+ty1+")" + " " + v.getOp2()+"("+ty2+")");
  }
  
  public void caseLtExpr(LtExpr v) {
    // G.v().out.println("    IfStmt(lt): v = "+v);
    setupSPFExpr(v);
    if( lvt.isLocalVariable(op1_str) ) {
      lvt.addUsedLocalVar(op1_str);
      // G.v().out.println("added usedLocalVar = " + op1_str);
    }
    ifExprStr_SPF = "new ComplexNonLinearIntegerExpression(" + 
      op1_str + ", LT, " + op2_str + ")"; 
    ifNotExprStr_SPF = "new ComplexNonLinearIntegerExpression(" + 
      op1_str + ", GE, " + op2_str + ")"; 
  }
  
  public void caseLeExpr(LeExpr v) {
    // G.v().out.println("    IfStmt(le): v = "+v);
    setupSPFExpr(v);
    if( lvt.isLocalVariable(op1_str) ) {
      lvt.addUsedLocalVar(op1_str);
      // G.v().out.println("added usedLocalVar = " + op1_str);
    }
    ifExprStr_SPF = "new ComplexNonLinearIntegerExpression(" + 
      op1_str + ", LE, " + op2_str + ")"; 
    ifNotExprStr_SPF = "new ComplexNonLinearIntegerExpression(" + 
      op1_str + ", GT, " + op2_str + ")"; 
  }
  public void caseNeExpr(NeExpr v) {
    // G.v().out.println("    IfStmt(ne): v = "+v);
    setupSPFExpr(v);
    if( lvt.isLocalVariable(op1_str) ) {
      lvt.addUsedLocalVar(op1_str);
      // G.v().out.println("added usedLocalVar = " + op1_str);
    }
    ifExprStr_SPF = "new ComplexNonLinearIntegerExpression(" + 
      op1_str + ", NE, " + op2_str + ")"; 
    ifNotExprStr_SPF = "new ComplexNonLinearIntegerExpression(" + 
      op1_str + ", EQ, " + op2_str + ")"; 
  }
  public void casePhiExpr(PhiExpr e) {
    List<ValueUnitPair> args = e.getArgs();
    assert(args.size() > 1);
    arg0PhiExpr = args.get(0).getValue().toString();
    arg1PhiExpr = args.get(1).getValue().toString();
  }
}
