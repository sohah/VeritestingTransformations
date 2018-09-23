package gov.nasa.jpf.symbc.veritesting.ast.transformations.arrayaccess;

import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.vm.ElementInfo;
import gov.nasa.jpf.vm.ThreadInfo;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.Operation;

import java.util.HashSet;

import static za.ac.sun.cs.green.expr.Operation.Operator.EQ;

public class ArrayVisitor extends AstMapVisitor {
    private DynamicRegion dynRegion;
    private ThreadInfo ti;
    private ArrayVisitor(ThreadInfo ti, DynamicRegion dynRegion) {
        super(new ExprMapVisitor());
        this.dynRegion = dynRegion;
        this.ti = ti;
    }

    public static DynamicRegion execute(ThreadInfo ti, DynamicRegion dynRegion) {
        ArrayVisitor visitor = new ArrayVisitor(ti, dynRegion);
        Stmt stmt = dynRegion.dynStmt.accept(visitor);
        return new DynamicRegion(dynRegion, stmt, new HashSet<>(), null);
    }

    @Override
    public Stmt visit(ArrayLoadInstruction c) {
        if (!IntConstant.class.isInstance(c.arrayref))
            throw new IllegalArgumentException("Cannot resolve symbolic array references");
        int arrayRef = ((IntConstant)c.arrayref).getValue();
        Expression rhs = null;
        ElementInfo eiArray = ti.getElementInfo(arrayRef);
        int len=(eiArray.getArrayFields()).arrayLength(); // assumed concrete
        if (IntConstant.class.isInstance(c.index)) {
            int index = ((IntConstant)c.index).getValue();
            if (index >= len) //TODO make this a SPF case in the future
                throw new IllegalArgumentException("Array index greater than or equal to array length");
            rhs = getArrayElement(eiArray, index);
        } else { // the index is symbolic
            rhs = constructArrayITE(eiArray, c.index, 0, len);
        }
        return new AssignmentStmt(c.def, rhs);
    }

    private Expression constructArrayITE(ElementInfo eiArray, Expression indexExpression, int index, int len) {
        if (index == len-1) return getArrayElement(eiArray, index);
        else {
            Expression cond = new Operation(EQ, indexExpression, new IntConstant(index));
            return new IfThenElseExpr(cond,
                    getArrayElement(eiArray, index),
                    constructArrayITE(eiArray, indexExpression, index+1, len));
        }
    }

    private Expression getArrayElement(ElementInfo ei, int index) {
        // copied from Soha's implementation of FillArrayLoadHoles in the previous veritesting implementation
        if(ei.getArrayType().equals("B")){
            return new IntConstant(ei.getByteElement(index)); //elements of the array are concrete
        }
        else if (ei.getArrayType().equals("I")){
            return new IntConstant(ei.getIntElement(index)); //elements of the array are concrete
        } else throw new IllegalArgumentException("Unsupported element type in array");
    }

    @Override
    public Stmt visit(ArrayStoreInstruction c) {
        return super.visit(c);
    }
}
