package gov.nasa.jpf.symbc.veritesting.ast.transformations.fieldaccess;

import com.ibm.wala.ssa.SSAGetInstruction;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.vm.*;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.RealConstant;

import java.util.Map;
import java.util.Objects;

import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.SPFToGreenExpr;

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
        return new DynamicRegion(dynRegion.staticRegion,
                stmt,
                dynRegion.varTypeTable,
                dynRegion.fieldRefTypeTable,
                dynRegion.slotParamTable,
                dynRegion.outputTable,
                dynRegion.isMethodRegion,
                dynRegion.spfCaseSet);
    }


    @Override
    public Stmt visit(PutInstruction putIns) {
        if (!IntConstant.class.isInstance(putIns.def))
            throw new IllegalArgumentException("Cannot handle symbolic object references in FieldSSAVisitor");
        else {
            FieldRef fieldRef = FieldRef.makePutFieldRef(ti, putIns);
            if (WalaVarExpr.class.isInstance(putIns.assignExpr)) {
                FieldRefVarExpr fieldRefVarExpr = new FieldRefVarExpr(fieldRef, createSubscript(fieldRef));
                if (dynRegion.varTypeTable.lookup(((WalaVarExpr)putIns.assignExpr).number) != null) {
                    dynRegion.fieldRefTypeTable.add(fieldRefVarExpr.getName(),
                            dynRegion.varTypeTable.lookup(((WalaVarExpr)putIns.assignExpr).number));
                }
                return new AssignmentStmt(fieldRefVarExpr, putIns.assignExpr);
            } else throw new IllegalArgumentException("Cannot handle PutInstruction with non-WalaVarExpr rhs");
        }
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
        else return stmt;
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
                compStmt = compose(compStmt, createGammaStmt(condition, elseFieldRef, elseSubscript,
                        new SubscriptPair(FIELD_SUBSCRIPT_BASE, gsm.createSubscript(elseFieldRef))));
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
        SubstituteGetOutput output = new SubstituteGetOutput(fieldRef).invoke();
        if (output.exceptionalMessage != null) throw new IllegalArgumentException(output.exceptionalMessage);
        FieldRefVarExpr fieldRefVarExpr = new FieldRefVarExpr(fieldRef, createSubscript(fieldRef));
        if (output.type != null) {
            dynRegion.fieldRefTypeTable.add(fieldRefVarExpr.getName(), output.type);
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
            FieldRef fieldRef = FieldRef.makeGetFieldRef(ti, c);
            if (psm.lookup(fieldRef) != null) {
                rhs = new FieldRefVarExpr(fieldRef, psm.lookup(fieldRef));
                if ((dynRegion.fieldRefTypeTable.lookup(((FieldRefVarExpr) rhs).getName())) != null)
                    type = (dynRegion.fieldRefTypeTable.lookup(((FieldRefVarExpr) rhs).getName()));
            }
            else {
                try {
                    SubstituteGetOutput output = substituteGet(c);
                    type = output.type;
                } catch (StaticRegionException e) {
                    exceptionalMessage = e.getMessage();
                }

            }
        } else exceptionalMessage = "encountered obj-ref in GetInstruction that is not a constant";
        // only one of rhs and exceptionalMessage should be non-null
        assert (rhs == null) ^ (exceptionalMessage == null);
        if (c.def instanceof WalaVarExpr)
            if (type != null) dynRegion.varTypeTable.add(((WalaVarExpr) c.def).number, type);
        else exceptionalMessage = "def not instance of WalaVarExpr in GetInstruction: " + c;
        if (exceptionalMessage != null) throw new IllegalArgumentException(exceptionalMessage);
        else return new AssignmentStmt(c.def, rhs);
    }

    private SubstituteGetOutput substituteGet(GetInstruction getIns)
            throws StaticRegionException {
        SubstituteGetOutput substituteGetOutput = new SubstituteGetOutput(FieldRef.makeGetFieldRef(ti, getIns)).invoke();
        String exceptionalMessage = substituteGetOutput.getExceptionalMessage();
        Expression def = substituteGetOutput.getDef();
        // only one of def and exceptionalMessage should be non-null
        assert (def == null) ^ (exceptionalMessage == null);
        if (exceptionalMessage != null) throw new StaticRegionException(exceptionalMessage);
        return substituteGetOutput;
    }

    private class SubstituteGetOutput {
        private FieldRef fieldRef;
        private String exceptionalMessage;
        private Expression def;
        private String type;

        SubstituteGetOutput(FieldRef fieldRef) {
            this.fieldRef = fieldRef;
        }

        String getExceptionalMessage() {
            return exceptionalMessage;
        }

        public Expression getDef() {
            return def;
        }

        public String getType() {
            return type;
        }

        public SubstituteGetOutput invoke() {
            final boolean isStatic = fieldRef.isStatic;
            int objRef;
            if (!isStatic) objRef = fieldRef.ref;
            else objRef = -1;
            String fieldName = fieldRef.field;
            String className = fieldRef.className;
            exceptionalMessage = null;
            def = null;
            type = null;
            if (objRef == 0) {
                exceptionalMessage = "java.lang.NullPointerException" + "referencing field '" + fieldName +
                        "' on null object";
            } else {
                ClassInfo ci = null;
                try {
                    ci = ClassLoaderInfo.getCurrentResolvedClassInfo(className);
                } catch (ClassInfoException e) {
                    exceptionalMessage = "fillFieldInputHole: class loader failed to resolve class name " +
                            className;
                }
                if (ci != null) {
                    ElementInfo eiFieldOwner;
                    if (!isStatic)
                        eiFieldOwner = ti.getElementInfo(objRef);
                    else
                        eiFieldOwner = ci.getStaticElementInfo();
                    if (eiFieldOwner == null) exceptionalMessage = "failed to resolve eiFieldOwner for field";
                    else {
                        FieldInfo fieldInfo;
                        if (!isStatic) fieldInfo = ci.getInstanceField(fieldName);
                        else fieldInfo = ci.getStaticField(fieldName);
                        if (fieldInfo == null) {
                            exceptionalMessage = "java.lang.NoSuchFieldError" + "referencing field '" + fieldName
                                    + "' in " + eiFieldOwner;
                        } else {
                            gov.nasa.jpf.symbc.numeric.Expression fieldAttr =
                                    (gov.nasa.jpf.symbc.numeric.Expression) eiFieldOwner.getFieldAttr(fieldInfo);
                            if (fieldAttr != null) {
                                def = SPFToGreenExpr(fieldAttr);
                            } else {
                                if (fieldInfo.getStorageSize() == 1) {
                                    if (fieldInfo.getType().equals("float")) {
                                        def = new RealConstant(Float.intBitsToFloat(eiFieldOwner.get1SlotField(fieldInfo)));
                                    }
                                    if (Objects.equals(fieldInfo.getType(), "int") ||
                                            Objects.equals(fieldInfo.getType(), "boolean") ||
                                            Objects.equals(fieldInfo.getType(), "byte") ||
                                            Objects.equals(fieldInfo.getType(), "char") ||
                                            Objects.equals(fieldInfo.getType(), "short"))
                                        def = new IntConstant(eiFieldOwner.get1SlotField(fieldInfo));
                                    if (fieldInfo.isReference())
                                        def = new IntConstant(eiFieldOwner.getReferenceField(fieldInfo));
                                } else {
                                    if (Objects.equals(fieldInfo.getType(), "double"))
                                        def = new RealConstant(Double.longBitsToDouble(eiFieldOwner.get2SlotField(fieldInfo)));
                                    if (Objects.equals(fieldInfo.getType(), "long"))
                                        def = new IntConstant((int) eiFieldOwner.get2SlotField(fieldInfo));
                                }
                                if (def == null) exceptionalMessage = "unsupported field type";
                                else type = fieldInfo.getType();
                            }
                        }
                    }
                }
            }
            return this;
        }
    }
}
