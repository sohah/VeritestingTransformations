package gov.nasa.jpf.symbc.veritesting.ast.transformations.arrayaccess;

import com.ibm.wala.ssa.SSAThrowInstruction;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.StatisticManager;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.SPFCases.SPFCaseList;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.fieldaccess.SubscriptPair;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.vm.ThreadInfo;
import za.ac.sun.cs.green.expr.*;

import java.util.Map;

import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.INSTANTIATION;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;
import static gov.nasa.jpf.symbc.veritesting.ast.transformations.arrayaccess.ArrayUtil.getInitialArrayValues;
import static za.ac.sun.cs.green.expr.Operation.Operator.*;

public class ArraySSAVisitor extends AstMapVisitor {
    private static int arrayExceptionNumber = 4242  ;
    private DynamicRegion dynRegion;
    private ThreadInfo ti;
    static final int ARRAY_SUBSCRIPT_BASE = 0;
    private GlobalArraySubscriptMap gsm;
    private StaticRegionException sre = null;
    // maps each array to its array of expressions on a path
    private ArrayExpressions arrayExpressions;

    private ArraySSAVisitor(ThreadInfo ti, DynamicRegion dynRegion) {
        super(new ExprMapVisitor());
        this.dynRegion = dynRegion;
        this.ti = ti;
        this.gsm = new GlobalArraySubscriptMap();
        this.arrayExpressions = new ArrayExpressions(ti);
    }

    public static DynamicRegion execute(ThreadInfo ti, DynamicRegion dynRegion) throws StaticRegionException {
        ArraySSAVisitor visitor = new ArraySSAVisitor(ti, dynRegion);
        Stmt stmt = dynRegion.dynStmt.accept(visitor);
        if (visitor.sre != null) throw visitor.sre;
        dynRegion.arrayOutputs = visitor.arrayExpressions;
        return new DynamicRegion(dynRegion, stmt, new SPFCaseList(), null, null,dynRegion.earlyReturnResult);
    }

    @Override
    public Stmt visit(ArrayLoadInstruction c) {
        String exceptionalMessage = null;
        Expression rhs = null;
        String type = null;
        Stmt assignStmt;
        ArrayRef arrayRef = ArrayRef.makeArrayRef(c);
        if (c.arrayref instanceof IntConstant) {
            if (isUnsupportedArrayRef(arrayRef)) return getThrowInstruction();
            rhs = arrayExpressions.get(arrayRef);
            type = arrayExpressions.getType(arrayRef.ref);
        } else exceptionalMessage = "encountered obj-ref in ArrayLoadInstruction that is not a constant";
        // only one of rhs and exceptionalMessage should be non-null
        assert (rhs == null) ^ (exceptionalMessage == null);
        if (c.def instanceof WalaVarExpr) {
            if (type != null) dynRegion.varTypeTable.add(((WalaVarExpr) c.def).number, type);
        }
        else exceptionalMessage = "def not instance of WalaVarExpr in GetInstruction: " + c;
        if (exceptionalMessage != null) throwException(new IllegalArgumentException(exceptionalMessage), INSTANTIATION);
        assignStmt = new AssignmentStmt(c.def, rhs);
        return getIfThenElseStmt(arrayRef, assignStmt);
    }

    private Stmt getIfThenElseStmt(ArrayRef arrayRef, Stmt assignStmt) {
        int len = ti.getElementInfo(arrayRef.ref).getArrayFields().arrayLength();
        Expression arrayInBoundsCond = new Operation(AND,
                new Operation(LT, arrayRef.index, new IntConstant(len)),
                new Operation(GE, arrayRef.index, new IntConstant(0)));
        StatisticManager.ArraySPFCaseCount++;
        return new IfThenElseStmt(null, arrayInBoundsCond, assignStmt, getThrowInstruction());
    }

    public static Stmt getThrowInstruction() {
        return new ThrowInstruction(new SSAThrowInstruction(-1, nextArrayExceptionNumber()) {});
    }

    public static int nextArrayExceptionNumber() {
        ++arrayExceptionNumber;
        return arrayExceptionNumber;
    }

    @Override
    public Stmt visit(ArrayStoreInstruction putIns) {
        if (!IntConstant.class.isInstance(putIns.arrayref)) {
            throwException(new IllegalArgumentException("Cannot handle symbolic object references in ArraySSAVisitor"), INSTANTIATION);
            return null;
        }
        else {
            ArrayRef arrayRef = ArrayRef.makeArrayRef(putIns);
            if (isUnsupportedArrayRef(arrayRef)) return getThrowInstruction();
            ArrayRefVarExpr arrayRefVarExpr = new ArrayRefVarExpr(arrayRef,
                    new SubscriptPair(-1, gsm.createSubscript(arrayRef.ref)));
            arrayExpressions.update(arrayRef, arrayRefVarExpr);
            Stmt assignStmt = new AssignmentStmt(arrayRefVarExpr, putIns.assignExpr);
            dynRegion.fieldRefTypeTable.add(arrayRefVarExpr.clone(), arrayExpressions.getType(arrayRef.ref));
            return getIfThenElseStmt(arrayRef, assignStmt);
        }
    }

    private boolean isUnsupportedArrayRef(ArrayRef arrayRef) {
        if (WalaVarExpr.class.isInstance(arrayRef.index))
            if (!dynRegion.varTypeTable.lookup(arrayRef.index).equals("int"))
                return true;
        if (arrayRef.ref == 0) {
            return true;
        }
        return false;
    }

    @Override
    public Stmt visit(IfThenElseStmt stmt) {
        ArrayExpressions oldExps = arrayExpressions.clone();
        Stmt newThen = stmt.thenStmt.accept(this);
        ArrayExpressions thenExps = arrayExpressions.clone();
        arrayExpressions = oldExps.clone();
        Stmt newElse = stmt.elseStmt.accept(this);
        ArrayExpressions elseExps = arrayExpressions.clone();
        arrayExpressions = oldExps.clone();
        Stmt gammaStmt;
        gammaStmt = mergeArrayExpressions(stmt.condition, thenExps, elseExps);
        if (gammaStmt != null)
            return new CompositionStmt(new IfThenElseStmt(stmt.original, stmt.condition, newThen, newElse), gammaStmt);
        else return new IfThenElseStmt(stmt.original, stmt.condition, newThen, newElse);
    }

    private Stmt mergeArrayExpressions(Expression condition, ArrayExpressions thenExps, ArrayExpressions elseExps) {
        Stmt compStmt = null;
        for (Map.Entry<Integer, Expression[]> entry : thenExps.table.entrySet()) {
            Integer thenArrayRef = entry.getKey();
            String type = thenExps.arrayTypesTable.get(thenArrayRef);
            Expression[] thenExpArr = entry.getValue();
            Expression[] elseExpArr = elseExps.lookup(thenArrayRef);
            if (elseExpArr != null) {
                assert elseExps.arrayTypesTable.get(thenArrayRef).equals(thenExps.arrayTypesTable.get(thenArrayRef));
                compStmt = compose(compStmt, createGammaStmtArray(thenArrayRef, condition, thenExpArr, elseExpArr, type));
                elseExps.remove(thenArrayRef);
            } else {
                compStmt = compose(compStmt, createGammaStmtArray(thenArrayRef, condition, thenExpArr,
                        getInitialArrayValues(ti, thenArrayRef).getFirst(), type));
            }
        }

        for (Map.Entry<Integer, Expression[]> entry : elseExps.table.entrySet()) {
            Integer elseArrayRef = entry.getKey();
            Expression[] elseExpArr = entry.getValue();
            String type = elseExps.arrayTypesTable.get(elseArrayRef);
            if (thenExps.lookup(elseArrayRef) != null) {
                throwException(new IllegalArgumentException("invariant failure: something in elseMap should not be in thenMap at this point"), INSTANTIATION);
            } else {
                compStmt = compose(compStmt, createGammaStmtArray(elseArrayRef, condition,
                        getInitialArrayValues(ti, elseArrayRef).getFirst(), elseExpArr, type));
            }
        }

        return compStmt;
    }

    private Stmt createGammaStmtArray(int ref, Expression condition, Expression[] thenExpArr, Expression[] elseExpArr,
                                      String type) {
        Stmt compStmt = null;
        assert thenExpArr.length == elseExpArr.length;
        for (int i=0; i < thenExpArr.length; i++){
            ArrayRef arrayRef = new ArrayRef(ref, new IntConstant(i));
            ArrayRefVarExpr lhs = new ArrayRefVarExpr(arrayRef,
                    new SubscriptPair(-1, gsm.createSubscript(ref)));
            dynRegion.fieldRefTypeTable.add(lhs, type);
            Stmt assignStmt = new AssignmentStmt(lhs, new GammaVarExpr(condition, thenExpArr[i], elseExpArr[i]));
            compStmt = compose(compStmt, assignStmt);
            arrayExpressions.update(arrayRef, lhs);
        }
        return compStmt;
    }

    private Stmt compose(Stmt s1, Stmt s2) {
        if (s1 == null && s2 == null)
            throwException(new IllegalArgumentException("trying to compose with two null statements"), INSTANTIATION);
        else if (s1 == null) return s2;
        else if (s2 == null) return s1;
        else return new CompositionStmt(s1, s2);
        return null;
    }
}
