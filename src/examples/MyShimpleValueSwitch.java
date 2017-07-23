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


class MyShimpleValueSwitch extends AbstractShimpleValueSwitch {
  String op1_str, op2_str, op;
	Type ty1, ty2;
	String ifExprStr_SPF, notIfExprStr_SPF;

	String getIfExprStr_SPF() { return ifExprStr_SPF; }
	
	String getNotIfExprStr_SPF() { return notIfExprStr_SPF; }	

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

  public void caseGtExpr(GtExpr v) {
		setupSPFExpr(v);
		ifExprStr_SPF = "new ComplexNonLinearIntegerExpression(" + op1_str + ", GT, " + op2_str + ")"; 
		notIfExprStr_SPF = "new ComplexNonLinearIntegerExpression(" + op1_str + ", LE, " + op2_str + ")"; 
		// G.v().out.println("    IfStmt(gt): v = "+v.getOp1()+"("+ty1+")" + " " + v.getOp2()+"("+ty2+")");
  }
  
	public void caseEqExpr(EqExpr v) {
    G.v().out.println("    IfStmt(eq): v = "+v);
  }
  public void caseGeExpr(GeExpr v) {
    G.v().out.println("    IfStmt(ge): v = "+v);
  }
  public void caseLtExpr(LtExpr v) {
    G.v().out.println("    IfStmt(lt): v = "+v);
  }
  public void caseLeExpr(LeExpr v) {
    G.v().out.println("    IfStmt(le): v = "+v);
  }
  public void caseNeExpr(NeExpr v) {
    G.v().out.println("    IfStmt(ne): v = "+v);
  }
}
