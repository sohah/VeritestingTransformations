package gov.nasa.jpf.symbc.veritesting.ast.transformations.phiToGamma;

import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import za.ac.sun.cs.green.expr.*;

import java.util.HashMap;
import java.util.Stack;



// God save the queen and those who invented visitors
public class PhiToGammaVisitor extends AstMapVisitor {

    private IfThenElseStmt lastIfThenElse = null;
    private HashMap<Expression, Expression> defToCondMap;
    private enum State {Then, Else}
    private class ITEState {
        IfThenElseStmt s; State state;
        public ITEState(IfThenElseStmt s, State state) {
            this.s = s;
            this.state = state;
        }
    }
    private Stack<ITEState> iteStateStack;

    public PhiToGammaVisitor() {
        super(new ExprMapVisitor());
        defToCondMap = new HashMap<>();
        iteStateStack = new Stack<>();
    }

    @Override
    public Stmt visit(IfThenElseStmt a) {
        lastIfThenElse = a;
        iteStateStack.push(new ITEState(a, State.Then));
        Stmt thenStmt = a.thenStmt.accept(this);
        iteStateStack.peek().state = State.Else;
        Stmt elseStmt = a.elseStmt.accept(this);
        iteStateStack.pop();
        return a;
    }

    @Override
    public Stmt visit(AssignmentStmt a) {
        if (iteStateStack.peek().state == State.Then)
            defToCondMap.put(a.lhs, lastIfThenElse.condition);
        if (iteStateStack.peek().state == State.Else)
            defToCondMap.put(a.lhs, new Operation(Operation.Operator.NOT, lastIfThenElse.condition));
        return a;
    }

    @Override
    public Stmt visit(ArrayLoadInstruction c) {
        defToCondMap.put(c.def, lastIfThenElse.condition);
        return c;
    }

    @Override
    public Stmt visit(ArrayStoreInstruction c) {
        //TODO create a new ArrayIndexExpr and use it in the map here after the array transformation is done
        //defToCondMap.put(new ArrayIndexExpr(c.arrayRef, c.index), lastIfThenElse.condition);
        return c;
    }

    @Override
    public Stmt visit(GetInstruction c) {
        defToCondMap.put(c.def, lastIfThenElse.condition);
        return c;
    }

    @Override
    public Stmt visit(PutInstruction c) {
        //TODO Create a FieldAccessExpr and use it here after the field transformation is done
        //defToCondMap.put(new FieldAccessExpr(c.def, c.field), lastIfThenElse.condition);
        return c;
    }

    @Override
    public Stmt visit(InvokeInstruction c) {
        for (int i = 0; i < c.result.length; i++) {
            defToCondMap.put(c.result[i], lastIfThenElse.condition);
        }
        return super.visit(c);
    }

    @Override
    public Stmt visit(ArrayLengthInstruction c) {
        defToCondMap.put(c.def, lastIfThenElse.condition);
        return super.visit(c);
    }

    @Override
    public Stmt visit(CheckCastInstruction c) {
        defToCondMap.put(c.result, lastIfThenElse.condition);
        return super.visit(c);
    }

    @Override
    public Stmt visit(InstanceOfInstruction c) {
        defToCondMap.put(c.result, lastIfThenElse.condition);
        return super.visit(c);
    }

    @Override
    public Stmt visit(PhiInstruction c) {
        //TODO add support for nested regions
        return new AssignmentStmt(c.def, new GammaVarExpr(this.defToCondMap.get(c.rhs[0]), c.rhs[0], c.rhs[1]));
    }
}
