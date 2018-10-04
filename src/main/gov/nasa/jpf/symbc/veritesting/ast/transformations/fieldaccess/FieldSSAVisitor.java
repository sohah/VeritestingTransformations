package gov.nasa.jpf.symbc.veritesting.ast.transformations.fieldaccess;

import com.ibm.wala.ssa.SSAGetInstruction;
import com.ibm.wala.ssa.SSAThrowInstruction;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.SPFCases.SPFCaseList;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.vm.*;
import za.ac.sun.cs.green.expr.*;

import java.util.HashSet;
import java.util.Map;
import java.util.Objects;

import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.SPFToGreenExpr;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.isConstant;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.getConstantType;

/*
A Path Subscript Map needs to be passed on from one statement to the other. Each statement updates or uses its PSM.
* A GetInstruction uses the PSM to replace itself with an AssignmentStmt that has a FieldRefVarExpr on the rhs.
* GetInstruction checks if the FieldRef is present in the PSM, if it is, it uses the last subscript to create a new
* FieldRefVarExpr, else it will create a subscript 1.
* A PutInstruction uses the PSM to replace itself with an AssignmentStmt that has a FieldRefVarExpr on the lhs.
PutInstruction checks if the FieldRef is present in the PSM, if it is, it creates a new PSM entry with the subscript
one higher than the last one, else it will create an entry with subscript 2.

This transformation pass should also construct gammas for field writes by merging the PSMs on the then and the else
side of an IfThenElseStmt. For merging the two PSMs, if a FieldRef appeared in both the thenPSM and the elsePSM, we
should create a gamma expression for that FieldRef from its latest subscripts.

The next transformation should do the FieldSubstitution to bring the actual field input values in. It will need to use a
expression visitor that replaces FieldRefVarExpr objects that have subscript 1 with the actual field value.
 */


public class FieldSSAVisitor extends AstMapVisitor {
    private static int fieldExceptionNumber=42424242;
    private DynamicRegion dynRegion;
    private FieldSubscriptMap psm;
    private ThreadInfo ti;
    static final int FIELD_SUBSCRIPT_BASE = 0;
    private GlobalSubscriptMap gsm;

    private FieldSSAVisitor(ThreadInfo ti, DynamicRegion dynRegion) {
        super(new ExprMapVisitor());
        this.dynRegion = dynRegion;
        this.psm = new FieldSubscriptMap();
        this.ti = ti;
        this.gsm = new GlobalSubscriptMap();
    }

    public static DynamicRegion execute(ThreadInfo ti, DynamicRegion dynRegion) {
        FieldSSAVisitor visitor = new FieldSSAVisitor(ti, dynRegion);
        Stmt stmt = dynRegion.dynStmt.accept(visitor);
        dynRegion.psm = visitor.psm;
        return new DynamicRegion(dynRegion, stmt, new SPFCaseList(), null, null);
    }


    @Override
    public Stmt visit(PutInstruction putIns) {
        if (!IntConstant.class.isInstance(putIns.def) && !putIns.getOriginal().isStatic())
            throw new IllegalArgumentException("Cannot handle symbolic object references in FieldSSAVisitor");
        else {
            FieldRef fieldRef;
            try {
                fieldRef = FieldRef.makePutFieldRef(ti, putIns);
            } catch (StaticRegionException e) {
                return getThrowInstruction();
            }
            FieldRefVarExpr fieldRefVarExpr = new FieldRefVarExpr(fieldRef, createSubscript(fieldRef));
            AssignmentStmt assignStmt = new AssignmentStmt(fieldRefVarExpr, putIns.assignExpr);
            String type = null;
            if (WalaVarExpr.class.isInstance(putIns.assignExpr)) {
                if (dynRegion.varTypeTable.lookup(putIns.assignExpr) != null) {
                    type = (String)dynRegion.varTypeTable.lookup(putIns.assignExpr);
                } else {
                    type = new SubstituteGetOutput(ti, fieldRef, true, null).invoke().type;
                }
            } else if (isConstant(putIns.assignExpr)) {
                type = getConstantType(putIns.assignExpr);
            } else if (IntVariable.class.isInstance(putIns.assignExpr)) {
                type = "int";
            } else if (RealVariable.class.isInstance(putIns.assignExpr)) {
                type = "float";
            }
            if (type != null)
                dynRegion.fieldRefTypeTable.add(fieldRefVarExpr.clone(), type);
            return assignStmt;
        }
    }

    public static Stmt getThrowInstruction() {
        return new ThrowInstruction(new SSAThrowInstruction(-1, nextFieldExceptionNumber()) {});
    }

    public static int nextFieldExceptionNumber() {
        ++fieldExceptionNumber;
        return fieldExceptionNumber;
    }


    private SubscriptPair createSubscript(FieldRef fieldRef) {
        SubscriptPair subscript = psm.lookup(fieldRef);
        if (subscript == null) {
            subscript = new SubscriptPair(FIELD_SUBSCRIPT_BASE+1, gsm.createSubscript(fieldRef));
            psm.add(fieldRef, subscript);
        } else {
            subscript = new SubscriptPair(subscript.pathSubscript+1, gsm.createSubscript(fieldRef));
            psm.updateValue(fieldRef, subscript);
        }
        return subscript;
    }


    @Override
    public Stmt visit(IfThenElseStmt stmt) {
        FieldSubscriptMap oldMap = psm.clone();
        Stmt newThen = stmt.thenStmt.accept(this);
        FieldSubscriptMap thenMap = psm.clone();
        psm = oldMap.clone();
        Stmt newElse = stmt.elseStmt.accept(this);
        FieldSubscriptMap elseMap = psm.clone();
        psm = oldMap.clone();
        Stmt gammaStmt = mergePSM(stmt.condition, thenMap, elseMap);
        if (gammaStmt != null)
            return new CompositionStmt(new IfThenElseStmt(stmt.original, stmt.condition, newThen, newElse), gammaStmt);
        else return new IfThenElseStmt(stmt.original, stmt.condition, newThen, newElse);
    }

    private Stmt mergePSM(Expression condition, FieldSubscriptMap thenMap, FieldSubscriptMap elseMap) {
        Stmt compStmt = null;
        for (Map.Entry<FieldRef, SubscriptPair> entry : thenMap.table.entrySet()) {
            FieldRef thenFieldRef = entry.getKey();
            SubscriptPair thenSubscript = entry.getValue();
            if (elseMap.lookup(thenFieldRef) != null) {
                compStmt = compose(compStmt, createGammaStmt(condition, thenFieldRef, thenSubscript,
                        elseMap.lookup(thenFieldRef)));
                elseMap.remove(thenFieldRef);
            } else {
                compStmt = compose(compStmt, createGammaStmt(condition, thenFieldRef, thenSubscript,
                        new SubscriptPair(FIELD_SUBSCRIPT_BASE, gsm.createSubscript(thenFieldRef))));
            }
        }

        for (Map.Entry<FieldRef, SubscriptPair> entry : elseMap.table.entrySet()) {
            FieldRef elseFieldRef = entry.getKey();
            SubscriptPair elseSubscript = entry.getValue();
            if (thenMap.lookup(elseFieldRef) != null) {
                throw new IllegalArgumentException("invariant failure: something in elseMap should not be in thenMap at this point");
            } else {
                compStmt = compose(compStmt, createGammaStmt(condition, elseFieldRef,
                        new SubscriptPair(FIELD_SUBSCRIPT_BASE, gsm.createSubscript(elseFieldRef)), elseSubscript));
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

    private Stmt createGammaStmt(Expression condition, FieldRef fieldRef, SubscriptPair thenSubscript,
                                 SubscriptPair elseSubscript) {
        if (thenSubscript.pathSubscript == FIELD_SUBSCRIPT_BASE && elseSubscript.pathSubscript == FIELD_SUBSCRIPT_BASE) {
            throw new IllegalArgumentException("invariant failure: ran into a gamma between subscripts that are both base subscripts");
        }
        SubstituteGetOutput output = new SubstituteGetOutput(ti, fieldRef, true, null).invoke();
        if (output.exceptionalMessage != null) throw new IllegalArgumentException(output.exceptionalMessage);
        FieldRefVarExpr fieldRefVarExpr = new FieldRefVarExpr(fieldRef, createSubscript(fieldRef));
        if (output.type != null) {
            dynRegion.fieldRefTypeTable.add(fieldRefVarExpr.clone(), output.type);
        }
        Expression thenExpr = thenSubscript.pathSubscript != FIELD_SUBSCRIPT_BASE ?
                new FieldRefVarExpr(fieldRef, thenSubscript) : output.def;
        Expression elseExpr = elseSubscript.pathSubscript != FIELD_SUBSCRIPT_BASE ?
                new FieldRefVarExpr(fieldRef, elseSubscript) : output.def;
        return new AssignmentStmt(fieldRefVarExpr, new GammaVarExpr(condition, thenExpr, elseExpr));
    }

    /*
    The solution to not have the same FieldRefVarExpr on both sides of a gamma is to map every FieldRef to its
    corresponding (path-specific subscript, global subscript). We should use this global subscript in the
    FieldRefVarExpr. Then when we create gammas, we will be able to create two separate FieldRefVarExpr objects on the
    latest path-specific subscript.
     */
    @Override
    public Stmt visit(GetInstruction c) {
        String exceptionalMessage = null;
        Expression rhs = null;
        String type = null;
        // If we are doing a get field from a constant object reference or if this field access is a static access,
        // we can fill this input in
        if ((c.ref instanceof IntConstant || ((SSAGetInstruction)c.original).isStatic())) {
            FieldRef fieldRef = null;
            try {
                fieldRef = FieldRef.makeGetFieldRef(ti, c);
            } catch (StaticRegionException e) {
                return getThrowInstruction();
            }
            if (psm.lookup(fieldRef) != null) {
                rhs = new FieldRefVarExpr(fieldRef, psm.lookup(fieldRef));
                if (dynRegion.fieldRefTypeTable.lookup(rhs) != null)
                    type = dynRegion.fieldRefTypeTable.lookup(rhs);
            }
            else {
                try {
                    SubstituteGetOutput output = substituteGet(c, fieldRef);
                    type = output.type;
                    rhs = output.def;
                } catch (StaticRegionException e) {
                    exceptionalMessage = e.getMessage();
                }

            }
        } else exceptionalMessage = "encountered obj-ref in GetInstruction that is not a constant";
        // only one of rhs and exceptionalMessage should be non-null
        assert (rhs == null) ^ (exceptionalMessage == null);
        if (c.def instanceof WalaVarExpr) {
            if (type != null) dynRegion.varTypeTable.add(((WalaVarExpr) c.def).number, type);
        }
        else exceptionalMessage = "def not instance of WalaVarExpr in GetInstruction: " + c;
        if (exceptionalMessage != null) throw new IllegalArgumentException(exceptionalMessage);
        else return new AssignmentStmt(c.def, rhs);
    }

    private SubstituteGetOutput substituteGet(GetInstruction getIns, FieldRef fieldRef)
            throws StaticRegionException {
        SubstituteGetOutput substituteGetOutput =
                new SubstituteGetOutput(ti, fieldRef, true, null).invoke();
        String exceptionalMessage = substituteGetOutput.getExceptionalMessage();
        Expression def = substituteGetOutput.getDef();
        // only one of def and exceptionalMessage should be non-null
        assert (def == null) ^ (exceptionalMessage == null);
        if (exceptionalMessage != null) throw new StaticRegionException(exceptionalMessage);
        return substituteGetOutput;
    }
}
