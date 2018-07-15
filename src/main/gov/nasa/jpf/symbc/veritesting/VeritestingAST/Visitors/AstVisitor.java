package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Visitors;

import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements.*;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.WALAInstructions.*;

public interface AstVisitor<T, S extends T>  extends ExprVisitor<S> {

    public T visit(AssignmentStmt a);
    public T visit(CompositionStmt a);
    public T visit(IfThenElseStmt a);
    public T visit(SkipStmt a);
    public T visit(SPFCaseStmt c);

    public T visit(ArrayLoadInstruction c);
    public T visit(ArrayStoreInstruction c);
    public T visit(BinaryOpInstruction c);
    public T visit(UnaryOpInstruction c);
    public T visit(ConversionInstruction c);
    public T visit(ComparisonInstruction c);
    public T visit(SwitchInstruction c);
    public T visit(ReturnInstruction c);
    public T visit(GetInstruction c);
    public T visit(PutInstruction c);
    public T visit(NewInstruction c);
    public T visit(InvokeInstruction c);
    public T visit(ArrayLengthInstruction c);
    public T visit(ThrowInstruction c);
    public T visit(CheckCastInstruction c);
    public T visit(InstanceOfInstruction c);
    public T visit(PhiInstruction c);

}
