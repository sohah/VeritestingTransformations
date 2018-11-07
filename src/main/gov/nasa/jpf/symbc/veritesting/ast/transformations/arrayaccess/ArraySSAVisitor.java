package gov.nasa.jpf.symbc.veritesting.ast.transformations.arrayaccess;

import com.ibm.wala.ssa.SSAThrowInstruction;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.StatisticManager;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.SPFCases.SPFCaseList;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.fieldaccess.SubscriptPair;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.vm.ElementInfo;
import gov.nasa.jpf.vm.ThreadInfo;
import za.ac.sun.cs.green.expr.*;

import java.util.Map;

import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.INSTANTIATION;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.*;
import static gov.nasa.jpf.symbc.veritesting.ast.def.ArrayRef.mergeArrayRefs;
import static gov.nasa.jpf.symbc.veritesting.ast.transformations.arrayaccess.ArrayUtil.getArrayElement;
import static gov.nasa.jpf.symbc.veritesting.ast.transformations.arrayaccess.ArrayUtil.getInitialArrayValues;
import static za.ac.sun.cs.green.expr.Operation.Operator.*;

public class ArraySSAVisitor extends AstMapVisitor {
    private static int arrayExceptionNumber = 4242  ;
    private DynamicRegion dynRegion;
    private ArraySubscriptMap psm;
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
        this.psm = new ArraySubscriptMap();
        this.gsm = new GlobalArraySubscriptMap();
        this.arrayExpressions = new ArrayExpressions(ti);
    }

    public static DynamicRegion execute(ThreadInfo ti, DynamicRegion dynRegion) throws StaticRegionException {
        ArraySSAVisitor visitor = new ArraySSAVisitor(ti, dynRegion);
        Stmt stmt = dynRegion.dynStmt.accept(visitor);
        if (visitor.sre != null) throw visitor.sre;
        dynRegion.arrayOutputs = visitor.arrayExpressions;
        return new DynamicRegion(dynRegion, stmt, new SPFCaseList(), null, null);
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
            /*if (psm.lookup(arrayRef) != null) {
                rhs = new ArrayRefVarExpr(arrayRef, psm.lookup(arrayRef));
                if (dynRegion.fieldRefTypeTable.lookup(rhs) != null)
                    type = dynRegion.fieldRefTypeTable.lookup(rhs);
            }
            else {
                Pair<Expression, String> p = getExpression(ti, arrayRef);
                rhs = p.getFirst();
                type = p.getSecond();
            }*/
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
            /*String type = null;
            if (WalaVarExpr.class.isInstance(putIns.assignExpr)) {
                if (dynRegion.varTypeTable.lookup(putIns.assignExpr) != null) {
                    type = (String)dynRegion.varTypeTable.lookup(putIns.assignExpr);
                } else {
                    type = (String) getExpression(ti, arrayRef).getSecond();
                }
            } else if (isConstant(putIns.assignExpr)) {
                type = getConstantType(putIns.assignExpr);
            } else if (IntVariable.class.isInstance(putIns.assignExpr)) {
                type = "int";
            } else if (RealVariable.class.isInstance(putIns.assignExpr)) {
                type = "float";
            }
            if (type != null)
                dynRegion.fieldRefTypeTable.add(arrayRefVarExpr.clone(), type);*/
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

    private SubscriptPair createSubscript(ArrayRef arrayRef) {
        SubscriptPair subscript = psm.lookup(arrayRef);
        if (subscript == null) {
            subscript = new SubscriptPair(ARRAY_SUBSCRIPT_BASE+1, gsm.createSubscript(arrayRef.ref));
            psm.add(arrayRef, subscript);
        } else {
            subscript = new SubscriptPair(subscript.pathSubscript+1, gsm.createSubscript(arrayRef.ref));
            psm.updateValue(arrayRef, subscript);
        }
        return subscript;
    }


    @Override
    public Stmt visit(IfThenElseStmt stmt) {
//        ArraySubscriptMap oldMap = psm.clone();
        ArrayExpressions oldExps = arrayExpressions.clone();
        Stmt newThen = stmt.thenStmt.accept(this);
//        ArraySubscriptMap thenMap = psm.clone();
        ArrayExpressions thenExps = arrayExpressions.clone();
//        psm = oldMap.clone();
        arrayExpressions = oldExps.clone();
        Stmt newElse = stmt.elseStmt.accept(this);
//        ArraySubscriptMap elseMap = psm.clone();
        ArrayExpressions elseExps = arrayExpressions.clone();
//        psm = oldMap.clone();
        arrayExpressions = oldExps.clone();
        Stmt gammaStmt;
//        try {
//            gammaStmt = mergePSM(stmt.condition, thenMap, elseMap);
            gammaStmt = mergeArrayExpressions(stmt.condition, thenExps, elseExps);
//        } catch (StaticRegionException e) {
//            sre = e;
//            return stmt;
//        }
        if (gammaStmt != null)
            return new CompositionStmt(new IfThenElseStmt(stmt.original, stmt.condition, newThen, newElse), gammaStmt);
        else return new IfThenElseStmt(stmt.original, stmt.condition, newThen, newElse);
    }

    private Stmt mergeArrayExpressions(Expression condition, ArrayExpressions thenExps, ArrayExpressions elseExps) {
        Stmt compStmt = null;
        for (Map.Entry<Integer, Expression[]> entry : thenExps.table.entrySet()) {
            Integer thenArrayRef = entry.getKey();
            assert elseExps.arrayTypesTable.get(thenArrayRef).equals(thenExps.arrayTypesTable.get(thenArrayRef));
            Expression[] thenExpArr = entry.getValue();
            Expression[] elseExpArr = elseExps.lookup(thenArrayRef);
            if (elseExpArr != null) {
                compStmt = compose(compStmt, createGammaStmtArray(thenArrayRef, condition, thenExpArr, elseExpArr));
                elseExps.remove(thenArrayRef);
            } else {
                compStmt = compose(compStmt, createGammaStmtArray(thenArrayRef, condition, thenExpArr, getInitialArrayValues(ti, thenArrayRef).getFirst()));
            }
        }

        for (Map.Entry<Integer, Expression[]> entry : elseExps.table.entrySet()) {
            Integer elseArrayRef = entry.getKey();
            Expression[] elseExpArr = entry.getValue();
            if (thenExps.lookup(elseArrayRef) != null) {
                throwException(new IllegalArgumentException("invariant failure: something in elseMap should not be in thenMap at this point"), INSTANTIATION);
            } else {
                compStmt = compose(compStmt, createGammaStmtArray(elseArrayRef, condition, getInitialArrayValues(ti, elseArrayRef).getFirst(), elseExpArr));
            }
        }

        return compStmt;
    }

    private Stmt createGammaStmtArray(int ref, Expression condition, Expression[] thenExpArr, Expression[] elseExpArr) {
        Stmt compStmt = null;
        assert thenExpArr.length == elseExpArr.length;
        for (int i=0; i < thenExpArr.length; i++){
            ArrayRef arrayRef = new ArrayRef(ref, new IntConstant(i));
            Expression lhs = new ArrayRefVarExpr(arrayRef,
                    new SubscriptPair(-1, gsm.createSubscript(ref)));
            Stmt assignStmt = new AssignmentStmt(lhs, new GammaVarExpr(condition, thenExpArr[i], elseExpArr[i]));
            compStmt = new CompositionStmt(compStmt, assignStmt);
            arrayExpressions.update(arrayRef, lhs);
        }
        return compStmt;
    }

    private Stmt mergePSM(Expression condition, ArraySubscriptMap thenMap, ArraySubscriptMap elseMap) throws StaticRegionException {
        Stmt compStmt = null;
        for (Map.Entry<ArrayRef, SubscriptPair> entry : thenMap.table.entrySet()) {
            ArrayRef thenArrayRef = entry.getKey();
            SubscriptPair thenSubscript = entry.getValue();
            SubscriptPair elseSubscript = elseMap.lookup(thenArrayRef);
            ArrayRef elseArrayRef = elseMap.lookupKey(thenArrayRef);
            if (elseSubscript != null) {
                assert elseArrayRef != null;
                compStmt = compose(compStmt, createGammaStmt(condition, thenArrayRef, elseArrayRef, thenSubscript,
                        elseSubscript));
                elseMap.remove(thenArrayRef);
            } else {
                assert elseArrayRef == null;
                compStmt = compose(compStmt, createGammaStmt(condition, thenArrayRef, null, thenSubscript,
                        new SubscriptPair(ARRAY_SUBSCRIPT_BASE, gsm.createSubscript(thenArrayRef.ref))));
            }
        }

        for (Map.Entry<ArrayRef, SubscriptPair> entry : elseMap.table.entrySet()) {
            ArrayRef elseArrayRef = entry.getKey();
            SubscriptPair elseSubscript = entry.getValue();
            if (thenMap.lookup(elseArrayRef) != null) {
                throwException(new IllegalArgumentException("invariant failure: something in elseMap should not be in thenMap at this point"), INSTANTIATION);
            } else {
                compStmt = compose(compStmt, createGammaStmt(condition, null, elseArrayRef,
                        new SubscriptPair(ARRAY_SUBSCRIPT_BASE, gsm.createSubscript(elseArrayRef.ref)), elseSubscript));
            }
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

    private Stmt createGammaStmt(Expression condition, ArrayRef thenArrayRef, ArrayRef elseArrayRef, SubscriptPair thenSubscript,
                                 SubscriptPair elseSubscript) throws StaticRegionException {
        if (thenSubscript.pathSubscript == ARRAY_SUBSCRIPT_BASE && elseSubscript.pathSubscript == ARRAY_SUBSCRIPT_BASE) {
            throwException(new IllegalArgumentException("invariant failure: ran into a gamma between subscripts that are both base subscripts"), INSTANTIATION);
        }
//        Pair<Expression, String> oldvalTypePair = getExpression(ti, thenArrayRef);
        Pair<Expression, String> oldvalTypePair = null;
        //TODO: if the indices were really merged, then construct a ITE to indicate that the new index is conditionally set to one of the two indices
        Pair<ArrayRef, Stmt> mergedrefStmtPair = mergeArrayRefs(condition, thenArrayRef, elseArrayRef);
//        ArrayRefVarExpr arrayRefVarExpr = new ArrayRefVarExpr(mergedrefStmtPair.getFirst(), createSubscript(thenArrayRef));
//        if (oldvalTypePair.getSecond() != null)
//            dynRegion.fieldRefTypeTable.add(arrayRefVarExpr.clone(), oldvalTypePair.getSecond());
        if (mergedrefStmtPair.getFirst().index instanceof WalaVarExpr)
            dynRegion.varTypeTable.add(mergedrefStmtPair.getFirst().index, "int");
        Expression thenExpr = thenSubscript.pathSubscript != ARRAY_SUBSCRIPT_BASE ?
                new ArrayRefVarExpr(thenArrayRef, thenSubscript) : oldvalTypePair.getFirst();
        Expression elseExpr = elseSubscript.pathSubscript != ARRAY_SUBSCRIPT_BASE ?
                new ArrayRefVarExpr(elseArrayRef, elseSubscript) : oldvalTypePair.getFirst();
        Expression assignExpr = new GammaVarExpr(condition, thenExpr, elseExpr);
        //TODO: get rid of this assignment statement. There should only be assignments to array entries. The left-hand side of each array entry should have a concrete index. These are generated by the makeAssignStmts() method.
        //TODO: Create equivalence-checks to test if array loads that appear after such assignment statements use the values assigned to by makeAssignStmts(). For this you will need to populate the concrete index ArrayRefVarExpr's into the PSM.
        Stmt retStmt = null; //new AssignmentStmt(arrayRefVarExpr, assignExpr);
        if (mergedrefStmtPair.getSecond() != null)
            retStmt = mergedrefStmtPair.getSecond();
        retStmt = makeAssignStmts(mergedrefStmtPair.getFirst(), assignExpr, retStmt, oldvalTypePair.getSecond());
        return retStmt;
    }

    private Stmt makeAssignStmts(ArrayRef mergedRef, Expression assignExpr, Stmt retStmt, String type) {
        ElementInfo eiArray = ti.getElementInfo(mergedRef.ref);
        Expression indexExp = mergedRef.index;
        int len=(eiArray.getArrayFields()).arrayLength(); // assumed concrete
        for (int i=0; i<len; i++) {
            Pair<Expression, String> p = getArrayElement(eiArray, i);
            Expression oldValue = p.getFirst();
            Expression cond = new Operation(EQ, indexExp, new IntConstant(i));
            Expression value = new GammaVarExpr(cond, assignExpr, oldValue);
            ArrayRef ref = new ArrayRef(mergedRef.ref, new IntConstant(i));
            ArrayRefVarExpr newExpr = new ArrayRefVarExpr(ref, createSubscript(ref));
            if (type != null)
                dynRegion.fieldRefTypeTable.add(newExpr, type);
            AssignmentStmt stmt = new AssignmentStmt(newExpr, value);
            retStmt = retStmt != null ? new CompositionStmt(retStmt, stmt) : stmt;
            if (p.getSecond() != null) {
                dynRegion.fieldRefTypeTable.add(newExpr, p.getSecond());
            }
        }
        return retStmt;
    }
}
