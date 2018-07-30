package gov.nasa.jpf.symbc.veritesting.ast.transformations.SPFCases;

import com.ibm.wala.ssa.*;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.DynamicEnvironment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import gov.nasa.jpf.vm.ArrayFields;
import gov.nasa.jpf.vm.ElementInfo;
import gov.nasa.jpf.vm.ThreadInfo;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.Operation;

import java.util.HashSet;


//SH: This is the first pass of SPFCases that creates SPFCases nodes. It assumes substitution has run.

public class SpfCasesPass1Visitor implements AstVisitor<Stmt> {
    private Expression spfCondition = Operation.TRUE;
    private ThreadInfo ti;

    public SpfCasesPass1Visitor(ThreadInfo ti){
        this.ti = ti;
    }


    @Override
    public Stmt visit(AssignmentStmt a) {
        return new AssignmentStmt(a.lhs, a.rhs);
    }

    @Override
    public Stmt visit(CompositionStmt a) {

        Stmt s1 = a.s1.accept(this);
        Stmt s2 = a.s2.accept(this);
        return new CompositionStmt(s1, s2);
    }

    @Override
    public Stmt visit(IfThenElseStmt a) {
        Stmt s;
        Expression oldSPFCondition = spfCondition;
        spfCondition = new Operation(Operation.Operator.AND, spfCondition, a.condition);
        Stmt thenStmt = a.thenStmt.accept(this);
        Stmt elseStmt = a.elseStmt.accept(this);
        s = new IfThenElseStmt(a.original, a.condition, thenStmt, elseStmt);
        spfCondition = oldSPFCondition;
        return s;
    }


    @Override
    public Stmt visit(SkipStmt a) {
        return SkipStmt.skip;
    }

    @Override
    public Stmt visit(SPFCaseStmt c) {
        return c;
    }

    @Override
    public Stmt visit(ArrayLoadInstruction c) {

        if(c.arrayref instanceof IntConstant) {
            int arrayRef = ((IntConstant) c.arrayref).getValue();
            ElementInfo ei = ti.getElementInfo(arrayRef);
            int arrayLength = ((ArrayFields) ei.getFields()).arrayLength();
            Expression lowBoundCondition = new Operation(Operation.Operator.GE, c.index, new IntConstant(0));
            Expression upperBoundCondition = new Operation(Operation.Operator.LT, c.index, new IntConstant(arrayLength));

            Expression arrayCcondition = new Operation(Operation.Operator.AND, lowBoundCondition, upperBoundCondition);

            Stmt thenStmt = new ArrayLoadInstruction((SSAArrayLoadInstruction) c.original,
                    c.arrayref,
                    c.index,
                    c.elementType,
                    c.def);

            Stmt elseStmt = new SPFCaseStmt(Operation.TRUE, SPFCaseStmt.SPFReason.OUT_OF_BOUND_EXCEPTION);

            SSAConditionalBranchInstruction dummy = new SSAConditionalBranchInstruction(-2, null, null, -2, -2, -2);

            return new IfThenElseStmt(dummy, arrayCcondition, thenStmt, elseStmt);
        }
        else{ //arrayRef was not substitutetd - something is wrong
            return new ArrayLoadInstruction((SSAArrayLoadInstruction) c.original,
                    c.arrayref,
                    c.index,
                    c.elementType,
                    c.def);
        }
    }


    @Override
    public Stmt visit(ArrayStoreInstruction c) {

        if(c.arrayref instanceof IntConstant) {
            int arrayRef = ((IntConstant) c.arrayref).getValue();
            ElementInfo ei = ti.getElementInfo(arrayRef);
            int arrayLength = ((ArrayFields) ei.getFields()).arrayLength();
            Expression lowBoundCondition = new Operation(Operation.Operator.GE, c.index, new IntConstant(0));
            Expression upperBoundCondition = new Operation(Operation.Operator.LT, c.index, new IntConstant(arrayLength));

            Expression arrayCcondition = new Operation(Operation.Operator.AND, lowBoundCondition, upperBoundCondition);

            Stmt thenStmt = new ArrayStoreInstruction((SSAArrayStoreInstruction) c.original,
                    c.arrayref,
                    c.index,
                    c.elementType,
                    c.assignExpr);

            Stmt elseStmt = new SPFCaseStmt(Operation.TRUE, SPFCaseStmt.SPFReason.OUT_OF_BOUND_EXCEPTION);

            SSAConditionalBranchInstruction dummy = new SSAConditionalBranchInstruction(-2, null, null, -2, -2, -2);

            return new IfThenElseStmt(dummy, arrayCcondition, thenStmt, elseStmt);
        }
        else{ //arrayRef was not substitutetd - something is wrong
            return new ArrayStoreInstruction((SSAArrayStoreInstruction) c.original,
                    c.arrayref,
                    c.index,
                    c.elementType,
                    c.assignExpr);
        }
    }

    @Override
    public Stmt visit(SwitchInstruction c) {
        return new SwitchInstruction((SSASwitchInstruction) c.original);
    }

    @Override
    public Stmt visit(ReturnInstruction c) {
        return new ReturnInstruction((SSAReturnInstruction) c.original,
                c.rhs);
    }

    @Override
    public Stmt visit(GetInstruction c) {
        return new GetInstruction((SSAGetInstruction) c.original,
                c.def,
                c.ref,
                c.field);
    }

    @Override
    public Stmt visit(PutInstruction c) {
        return new PutInstruction((SSAPutInstruction) c.original,
                c.def,
                c.field,
                c.assignExpr);
    }

    @Override
    public Stmt visit(NewInstruction c) {
        return new SPFCaseStmt(spfCondition,
                SPFCaseStmt.SPFReason.OBJECT_CREATION);
    }

    @Override
    public Stmt visit(InvokeInstruction c) {
        return new InvokeInstruction((SSAInvokeInstruction) c.original,
                c.result,
                c.params);
    }

    @Override
    public Stmt visit(ArrayLengthInstruction c) {
        return new ArrayLengthInstruction((SSAArrayLengthInstruction) c.original,
                c.arrayref,
                c.def);
    }

    @Override
    public Stmt visit(ThrowInstruction c) {
        return new SPFCaseStmt(spfCondition,
                SPFCaseStmt.SPFReason.THROW);
    }

    @Override
    public Stmt visit(CheckCastInstruction c) {
        return new CheckCastInstruction(
                (SSACheckCastInstruction) c.original,
                c.result,
                c.val,
                c.declaredResultTypes);
    }

    @Override
    public Stmt visit(InstanceOfInstruction c) {
        return new InstanceOfInstruction((SSAInstanceofInstruction) c.original,
                c.result,
                c.val,
                c.checkedType);
    }

    @Override
    public Stmt visit(PhiInstruction c) {
        return new PhiInstruction(c.getOriginal(),
                c.def,
                c.rhs);
    }

    public static DynamicRegion execute(ThreadInfo ti, DynamicRegion dynRegion) {
        SpfCasesPass1Visitor visitor = new SpfCasesPass1Visitor(ti);
        Stmt dynStmt = dynRegion.dynStmt.accept(visitor);
        return new DynamicRegion(dynRegion.staticRegion,
                dynStmt,
                dynRegion.slotTypeTable,
                dynRegion.varTypeTable,
                dynRegion.valueSymbolTable,
                dynRegion.slotParamTable,
                dynRegion.outputTable,
                new HashSet<>());
    }
}
