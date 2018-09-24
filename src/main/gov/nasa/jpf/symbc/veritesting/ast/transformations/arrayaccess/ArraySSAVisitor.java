package gov.nasa.jpf.symbc.veritesting.ast.transformations.arrayaccess;

import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.fieldaccess.SubscriptPair;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.vm.ElementInfo;
import gov.nasa.jpf.vm.ThreadInfo;
import za.ac.sun.cs.green.expr.*;

import java.util.HashSet;
import java.util.Map;

import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.getConstantType;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.isConstant;
import static za.ac.sun.cs.green.expr.Operation.Operator.EQ;

public class ArraySSAVisitor extends AstMapVisitor {
    private DynamicRegion dynRegion;
    private ArraySubscriptMap psm;
    private ThreadInfo ti;
    static final int ARRAY_SUBSCRIPT_BASE = 0;
    private GlobalArraySubscriptMap gsm;

    private ArraySSAVisitor(ThreadInfo ti, DynamicRegion dynRegion) {
        super(new ExprMapVisitor());
        this.dynRegion = dynRegion;
        this.ti = ti;
        this.psm = new ArraySubscriptMap();
        this.gsm = new GlobalArraySubscriptMap();
    }

    public static DynamicRegion execute(ThreadInfo ti, DynamicRegion dynRegion) {
        ArraySSAVisitor visitor = new ArraySSAVisitor(ti, dynRegion);
        Stmt stmt = dynRegion.dynStmt.accept(visitor);
        dynRegion.arrayPSM = visitor.psm;
        return new DynamicRegion(dynRegion, stmt, new HashSet<>(), null);
    }

    @Override
    public Stmt visit(ArrayLoadInstruction c) {
        String exceptionalMessage = null;
        Expression rhs = null;
        String type = null;
        ArrayRef arrayRef = ArrayRef.makeArrayRef(c);
        if (c.arrayref instanceof IntConstant) {
            if (psm.lookup(arrayRef) != null) {
                rhs = new ArrayRefVarExpr(arrayRef, psm.lookup(arrayRef));
                if (dynRegion.fieldRefTypeTable.lookup(rhs) != null)
                    type = dynRegion.fieldRefTypeTable.lookup(rhs);
            }
            else {
                Pair<Expression, String> p = getExpression(arrayRef);
                rhs = p.getFirst();
                type = p.getSecond();
            }
        } else exceptionalMessage = "encountered obj-ref in ArrayLoadInstruction that is not a constant";
        // only one of rhs and exceptionalMessage should be non-null
        assert (rhs == null) ^ (exceptionalMessage == null);
        if (c.def instanceof WalaVarExpr) {
            if (type != null) dynRegion.varTypeTable.add(((WalaVarExpr) c.def).number, type);
        }
        else exceptionalMessage = "def not instance of WalaVarExpr in GetInstruction: " + c;
        if (exceptionalMessage != null) throw new IllegalArgumentException(exceptionalMessage);
        else return new AssignmentStmt(c.def, rhs);
    }

    private Pair getExpression(ArrayRef c) {
        Pair rhs;
        ElementInfo eiArray = ti.getElementInfo(c.ref);
        int len=(eiArray.getArrayFields()).arrayLength(); // assumed concrete
        if (IntConstant.class.isInstance(c.index)) {
            int index = ((IntConstant)c.index).getValue();
            if (index >= len) //TODO make this a SPF case in the future
                throw new IllegalArgumentException("Array index greater than or equal to array length");
            rhs = getArrayElement(eiArray, index);
        } else { // the index is symbolic
            rhs = constructArrayITE(eiArray, c.index, 0, len);
        }
        return rhs;
    }


    private Pair constructArrayITE(ElementInfo eiArray, Expression indexExpression, int index, int len) {
        if (index == len-1) return getArrayElement(eiArray, index);
        else {
            Expression cond = new Operation(EQ, indexExpression, new IntConstant(index));
            Pair<Expression, String> elem = getArrayElement(eiArray, index);
            Expression ite = (Expression) constructArrayITE(eiArray, indexExpression, index+1, len).getFirst();
            return new Pair(new IfThenElseExpr(cond, elem.getFirst(), ite), elem.getSecond());
        }
    }

    public static Pair getArrayElement(ElementInfo ei, int index) {
        // copied from Soha's implementation of FillArrayLoadHoles in the previous veritesting implementation
        if(ei.getArrayType().equals("B")){
            return new Pair(new IntConstant(ei.getByteElement(index)), "int"); //elements of the array are concrete
        }
        else if (ei.getArrayType().equals("I")){
            return new Pair(new IntConstant(ei.getIntElement(index)), "int"); //elements of the array are concrete
        } else if (ei.getArrayType().equals("F")){
            return new Pair(new RealConstant(ei.getFloatElement(index)), "real"); //elements of the array are concrete
        } else if (ei.getArrayType().equals("D")){
            return new Pair(new RealConstant(ei.getDoubleElement(index)), "real"); //elements of the array are concrete
        } else throw new IllegalArgumentException("Unsupported element type in array");
    }

    public static void doArrayStore(ThreadInfo ti, ArrayRef arrayRef, Expression assignExpr) {
        ElementInfo eiArray = ti.getElementInfo(arrayRef.ref);
        int len=(eiArray.getArrayFields()).arrayLength(); // assumed concrete
        Expression indexExp = arrayRef.index;
        if (IntConstant.class.isInstance(indexExp)) {
            int index = ((IntConstant)indexExp).getValue();
            if (index >= len) //TODO make this a SPF case in the future
                throw new IllegalArgumentException("Array index greater than or equal to array length");
            eiArray.checkArrayBounds(index);
            eiArray.setIntElement(index, 0);
            eiArray.setElementAttrNoClone(index, assignExpr);
        } else { // the index is symbolic
            for (int i=0; i<len; i++) {
                Pair<Expression, String> p = getArrayElement(eiArray, i);
                Expression oldValue = p.getFirst();
                Expression value = new IfThenElseExpr(new Operation(EQ, indexExp, new IntConstant(i)),
                        assignExpr, oldValue);
                eiArray.checkArrayBounds(i);
                eiArray.setIntElement(i, 0);
                eiArray.setElementAttrNoClone(i, value);
            }
        }
    }

    @Override
    public Stmt visit(ArrayStoreInstruction putIns) {
        if (!IntConstant.class.isInstance(putIns.arrayref))
            throw new IllegalArgumentException("Cannot handle symbolic object references in ArraySSAVisitor");
        else {
            ArrayRef arrayRef = ArrayRef.makeArrayRef(putIns);
            ArrayRefVarExpr arrayRefVarExpr = new ArrayRefVarExpr(arrayRef, createSubscript(arrayRef));
            AssignmentStmt assignStmt = new AssignmentStmt(arrayRefVarExpr, putIns.assignExpr);
            String type = null;
            if (WalaVarExpr.class.isInstance(putIns.assignExpr)) {
                if (dynRegion.varTypeTable.lookup(putIns.assignExpr) != null) {
                    type = (String)dynRegion.varTypeTable.lookup(putIns.assignExpr);
                } else {
                    type = (String) getExpression(arrayRef).getSecond();
                }
            } else if (isConstant(putIns.assignExpr)) {
                type = getConstantType(putIns.assignExpr);
            } else if (IntVariable.class.isInstance(putIns.assignExpr)) {
                type = "int";
            } else if (RealVariable.class.isInstance(putIns.assignExpr)) {
                type = "float";
            }
            if (type != null)
                dynRegion.fieldRefTypeTable.add(arrayRefVarExpr.clone(), type);
            return assignStmt;
        }
    }

    private SubscriptPair createSubscript(ArrayRef arrayRef) {
        SubscriptPair subscript = psm.lookup(arrayRef);
        if (subscript == null) {
            subscript = new SubscriptPair(ARRAY_SUBSCRIPT_BASE+1, gsm.createSubscript(arrayRef));
            psm.add(arrayRef, subscript);
        } else {
            subscript = new SubscriptPair(subscript.pathSubscript+1, gsm.createSubscript(arrayRef));
            psm.updateValue(arrayRef, subscript);
        }
        return subscript;
    }


    @Override
    public Stmt visit(IfThenElseStmt stmt) {
        ArraySubscriptMap oldMap = psm.clone();
        Stmt newThen = stmt.thenStmt.accept(this);
        ArraySubscriptMap thenMap = psm.clone();
        psm = oldMap.clone();
        Stmt newElse = stmt.elseStmt.accept(this);
        ArraySubscriptMap elseMap = psm.clone();
        psm = oldMap.clone();
        Stmt gammaStmt = mergePSM(stmt.condition, thenMap, elseMap);
        if (gammaStmt != null)
            return new CompositionStmt(new IfThenElseStmt(stmt.original, stmt.condition, newThen, newElse), gammaStmt);
        else return new IfThenElseStmt(stmt.original, stmt.condition, newThen, newElse);
    }

    private Stmt mergePSM(Expression condition, ArraySubscriptMap thenMap, ArraySubscriptMap elseMap) {
        Stmt compStmt = null;
        for (Map.Entry<ArrayRef, SubscriptPair> entry : thenMap.table.entrySet()) {
            ArrayRef thenFieldRef = entry.getKey();
            SubscriptPair thenSubscript = entry.getValue();
            if (elseMap.lookup(thenFieldRef) != null) {
                compStmt = compose(compStmt, createGammaStmt(condition, thenFieldRef, thenSubscript,
                        elseMap.lookup(thenFieldRef)));
                elseMap.remove(thenFieldRef);
            } else {
                compStmt = compose(compStmt, createGammaStmt(condition, thenFieldRef, thenSubscript,
                        new SubscriptPair(ARRAY_SUBSCRIPT_BASE, gsm.createSubscript(thenFieldRef))));
            }
        }

        for (Map.Entry<ArrayRef, SubscriptPair> entry : elseMap.table.entrySet()) {
            ArrayRef elseFieldRef = entry.getKey();
            SubscriptPair elseSubscript = entry.getValue();
            if (thenMap.lookup(elseFieldRef) != null) {
                throw new IllegalArgumentException("invariant failure: something in elseMap should not be in thenMap at this point");
            } else {
                compStmt = compose(compStmt, createGammaStmt(condition, elseFieldRef,
                        new SubscriptPair(ARRAY_SUBSCRIPT_BASE, gsm.createSubscript(elseFieldRef)), elseSubscript));
            }
        }

        return compStmt;
    }

    private Stmt compose(Stmt s1, Stmt s2) {
        if (s1 == null && s2 == null)
            throw new IllegalArgumentException("trying to compose with two null statements");
        else if (s1 == null) return s2;
        else if (s2 == null) return s1;
        else return new CompositionStmt(s1, s2);
    }

    private Stmt createGammaStmt(Expression condition, ArrayRef arrayRef, SubscriptPair thenSubscript,
                                 SubscriptPair elseSubscript) {
        if (thenSubscript.pathSubscript == ARRAY_SUBSCRIPT_BASE && elseSubscript.pathSubscript == ARRAY_SUBSCRIPT_BASE) {
            throw new IllegalArgumentException("invariant failure: ran into a gamma between subscripts that are both base subscripts");
        }
        Pair<Expression, String> pair = getExpression(arrayRef);
        ArrayRefVarExpr arrayRefVarExpr = new ArrayRefVarExpr(arrayRef, createSubscript(arrayRef));
        if (pair.getSecond() != null) {
            dynRegion.fieldRefTypeTable.add(arrayRefVarExpr.clone(), pair.getSecond());
        }
        Expression thenExpr = thenSubscript.pathSubscript != ARRAY_SUBSCRIPT_BASE ?
                new ArrayRefVarExpr(arrayRef, thenSubscript) : pair.getFirst();
        Expression elseExpr = elseSubscript.pathSubscript != ARRAY_SUBSCRIPT_BASE ?
                new ArrayRefVarExpr(arrayRef, elseSubscript) : pair.getFirst();
        return new AssignmentStmt(arrayRefVarExpr, new GammaVarExpr(condition, thenExpr, elseExpr));
    }
}
