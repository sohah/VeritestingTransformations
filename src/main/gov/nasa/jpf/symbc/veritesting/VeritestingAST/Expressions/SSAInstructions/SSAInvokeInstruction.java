
package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.SSAInstructions;

import com.ibm.wala.classLoader.CallSiteReference;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.Var;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpression;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpressionVisitor;

public class SSAInvokeInstruction implements VeriExpression {

  private final int iindex;
  private final Var result;
  private final VeriExpression[] params;
  private final int exception;
  private final CallSiteReference site;
  private final boolean isVoidReturn;

  /**
   * The value numbers of the arguments passed to the call. For non-static methods, params[0] == this. If params == null, this
   * should be a static method with no parameters.
   */

  protected SSAInvokeInstruction(int iindex, Var result, VeriExpression[] params, int exception, CallSiteReference site, boolean isVoidReturn) {

    this.iindex = iindex;
    this.result = result;
    this.params = params;
    this.exception = exception;
    this.site = site;
    this.isVoidReturn = isVoidReturn;
  }


  public Var getReturnValue(int i) {
    assert (!isVoidReturn);
    return result;
  }

  @Override
  public void visit(VeriExpressionVisitor v) {
    v.visitInvokeSSA(this);
  }

  public int getIindex() {
    return iindex;
  }

  public VeriExpression[] getParams() {
    return params;
  }

  public int getException() {
    return exception;
  }

  public boolean isVoidReturn() {
    return isVoidReturn;
  }

  public CallSiteReference getSite() {
    return site;
  }
}