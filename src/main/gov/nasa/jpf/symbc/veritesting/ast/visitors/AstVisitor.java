package gov.nasa.jpf.symbc.veritesting.ast.visitors;

import gov.nasa.jpf.symbc.veritesting.ast.def.SPFCaseStmt;
import gov.nasa.jpf.symbc.veritesting.ast.def.UnaryOpInstruction;

public interface AstVisitor<T, S extends T>  extends ExprVisitor<S> {

    public T visit(gov.nasa.jpf.symbc.veritesting.ast.def.AssignmentStmt a);
    public T visit(gov.nasa.jpf.symbc.veritesting.ast.def.CompositionStmt a);
    public T visit(gov.nasa.jpf.symbc.veritesting.ast.def.IfThenElseStmt a);
    public T visit(gov.nasa.jpf.symbc.veritesting.ast.def.SkipStmt a);
    public T visit(SPFCaseStmt c);

    public T visit(gov.nasa.jpf.symbc.veritesting.ast.def.ArrayLoadInstruction c);
    public T visit(gov.nasa.jpf.symbc.veritesting.ast.def.ArrayStoreInstruction c);
    public T visit(gov.nasa.jpf.symbc.veritesting.ast.def.BinaryOpInstruction c);
    public T visit(UnaryOpInstruction c);
    public T visit(gov.nasa.jpf.symbc.veritesting.ast.def.ConversionInstruction c);
    public T visit(gov.nasa.jpf.symbc.veritesting.ast.def.ComparisonInstruction c);
    public T visit(gov.nasa.jpf.symbc.veritesting.ast.def.SwitchInstruction c);
    public T visit(gov.nasa.jpf.symbc.veritesting.ast.def.ReturnInstruction c);
    public T visit(gov.nasa.jpf.symbc.veritesting.ast.def.GetInstruction c);
    public T visit(gov.nasa.jpf.symbc.veritesting.ast.def.PutInstruction c);
    public T visit(gov.nasa.jpf.symbc.veritesting.ast.def.NewInstruction c);
    public T visit(gov.nasa.jpf.symbc.veritesting.ast.def.InvokeInstruction c);
    public T visit(gov.nasa.jpf.symbc.veritesting.ast.def.ArrayLengthInstruction c);
    public T visit(gov.nasa.jpf.symbc.veritesting.ast.def.ThrowInstruction c);
    public T visit(gov.nasa.jpf.symbc.veritesting.ast.def.CheckCastInstruction c);
    public T visit(gov.nasa.jpf.symbc.veritesting.ast.def.InstanceOfInstruction c);
    public T visit(gov.nasa.jpf.symbc.veritesting.ast.def.PhiInstruction c);

}
