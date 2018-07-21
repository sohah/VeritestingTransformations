package gov.nasa.jpf.symbc.veritesting.ast.transformations.SPFCases;

import com.ibm.wala.ssa.*;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import ia_parser.Exp;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Operation;


//SH: This is the SPFCases visitor that turns some statements, like object creation and throw instructions into
// SPFCases, upon doing so, unncessary compsoed statements with SPFCases are eliminated.

public class SpfCasesVisitor implements AstVisitor<Stmt> {
    Expression spfCondition = Operation.TRUE;


    @Override
    public Stmt visit(AssignmentStmt a) {
        return new AssignmentStmt(a.lhs, a.rhs);
    }

    @Override
    public Stmt visit(CompositionStmt a) {

        Stmt s1 = a.s1.accept(this);
        Stmt s2 = a.s2.accept(this);
        if (s1 instanceof SPFCaseStmt)
            return s1;
        else if (s2 instanceof SPFCaseStmt)
            return s2;
        else
            return new CompositionStmt(s1, s2);
    }

    @Override
    public Stmt visit(IfThenElseStmt a) {
        Stmt s;
        Expression oldSPFCondition = spfCondition;
        spfCondition = new Operation(Operation.Operator.AND, spfCondition, a.condition);
        Stmt thenStmt = a.thenStmt.accept(this);
        Stmt elseStmt = a.elseStmt.accept(this);
        if ((thenStmt instanceof SPFCaseStmt) && (elseStmt instanceof SPFCaseStmt)) //attempting to collapse unncessary nodes
            s = new SPFCaseStmt(oldSPFCondition, SPFCaseStmt.SPFReason.MULTIPLE);
        else if ((thenStmt instanceof SPFCaseStmt) && (elseStmt.equals(SkipStmt.skip)))
            s = thenStmt;
        else if ((elseStmt instanceof SPFCaseStmt) && (thenStmt.equals(SkipStmt.skip)))
            s = elseStmt;
        else
            s = new IfThenElseStmt(a.original, a.condition, thenStmt, elseStmt);
        spfCondition=oldSPFCondition;
        return s;
    }




@Override
public Stmt visit(SkipStmt a){
        return SkipStmt.skip;
        }

@Override
public Stmt visit(SPFCaseStmt c){
        return c;
        }

@Override
public Stmt visit(ArrayLoadInstruction c){
        return new ArrayLoadInstruction((SSAArrayLoadInstruction)c.original,
        c.arrayref,
        c.index,
        c.elementType,
        c.def);
        }

@Override
public Stmt visit(ArrayStoreInstruction c){
        return new ArrayStoreInstruction((SSAArrayStoreInstruction)c.original,
        c.arrayref,
        c.index,
        c.elementType,
        c.assignExpr);
        }

@Override
public Stmt visit(SwitchInstruction c){
        return new SwitchInstruction((SSASwitchInstruction)c.original);
        }

@Override
public Stmt visit(ReturnInstruction c){
        return new ReturnInstruction((SSAReturnInstruction)c.original,
        c.rhs);
        }

@Override
public Stmt visit(GetInstruction c){
        return new GetInstruction((SSAGetInstruction)c.original,
        c.def,
        c.ref,
        c.field);
        }

@Override
public Stmt visit(PutInstruction c){
        return new PutInstruction((SSAPutInstruction)c.original,
        c.def,
        c.field,
        c.assignExpr);
        }

@Override
public Stmt visit(NewInstruction c){
        return new SPFCaseStmt(spfCondition,
        SPFCaseStmt.SPFReason.OBJECT_CREATION);
        }

@Override
public Stmt visit(InvokeInstruction c){
        return new InvokeInstruction((SSAInvokeInstruction)c.original,
        c.result,
        c.params);
        }

@Override
public Stmt visit(ArrayLengthInstruction c){
        return new ArrayLengthInstruction((SSAArrayLengthInstruction)c.original,
        c.arrayref,
        c.def);
        }

@Override
public Stmt visit(ThrowInstruction c){
        return new SPFCaseStmt(spfCondition,
        SPFCaseStmt.SPFReason.THROW);
        }

@Override
public Stmt visit(CheckCastInstruction c){
        return new CheckCastInstruction(
        (SSACheckCastInstruction)c.original,
        c.result,
        c.val,
        c.declaredResultTypes);
        }

@Override
public Stmt visit(InstanceOfInstruction c){
        return new InstanceOfInstruction((SSAInstanceofInstruction)c.original,
        c.result,
        c.val,
        c.checkedType);
        }

@Override
public Stmt visit(PhiInstruction c){
        return new PhiInstruction(c.getOriginal(),
        c.def,
        c.rhs);
        }
        }
