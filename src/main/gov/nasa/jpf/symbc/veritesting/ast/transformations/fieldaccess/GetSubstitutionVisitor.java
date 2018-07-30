package gov.nasa.jpf.symbc.veritesting.ast.transformations.fieldaccess;

import com.ibm.wala.ssa.SSAGetInstruction;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.GetInstruction;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StackSlotTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution.SlotTypeTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution.ValueSymbolTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.typepropagation.WalaNumTypesTable;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.vm.*;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.RealConstant;


import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.SPFToGreenExpr;

public class GetSubstitutionVisitor extends AstMapVisitor {
    private ValueSymbolTable valueSymbolTable;
    private ThreadInfo ti;
    private final StackSlotTable stackSlotTable;
    private SlotTypeTable slotTypeTable;
    private WalaNumTypesTable walaNumTypesTable;
    public GetSubstitutionVisitor(ThreadInfo ti, ValueSymbolTable valueSymbolTable, StackSlotTable stackSlotTable,
                                  SlotTypeTable slotTypeTable, WalaNumTypesTable walaNumTypesTable) {
        super(new ExprMapVisitor());
        this.ti = ti;
        this.valueSymbolTable = valueSymbolTable;
        this.stackSlotTable = stackSlotTable;
        this.slotTypeTable = slotTypeTable;
        this.walaNumTypesTable = walaNumTypesTable;
    }

    public static DynamicRegion doSubstitution(ThreadInfo ti, DynamicRegion dynRegion) {
        GetSubstitutionVisitor visitor = new GetSubstitutionVisitor(ti,
                dynRegion.valueSymbolTable, dynRegion.stackSlotTable, dynRegion.slotTypeTable, dynRegion.walaNumTypesTable);
        Stmt dynStmt = dynRegion.dynStmt.accept(visitor);
        return new DynamicRegion(dynRegion.staticRegion, dynStmt, visitor.slotTypeTable, visitor.valueSymbolTable, visitor.walaNumTypesTable);
    }

    @Override
    public Stmt visit(GetInstruction c) {
        String exceptionalMessage = null;
        Expression def = null;
        // If we are doing a get field from a constant object reference or if this field access is a static access,
        // we can fill this input in
        if ((c.ref instanceof IntConstant || ((SSAGetInstruction)c.original).isStatic())) {
            if (c.def instanceof WalaVarExpr) {
                try {
                    int number = ((WalaVarExpr) c.def).number;
                    def = substituteGet(c);
                    valueSymbolTable.add(number, def);
                } catch (StaticRegionException e) {
                    exceptionalMessage = e.getMessage();
                }

            } else exceptionalMessage = "def not instance of WalaVarExpr in GetInstruction: " + c;
        } else exceptionalMessage = "encountered obj-ref in non-static GetInstruction that is not a constant";
        // only one of def and exceptionalMessage should be non-null
        assert (def == null) ^ (exceptionalMessage == null);
        if (exceptionalMessage != null) throw new IllegalArgumentException(exceptionalMessage);
        else return new GetInstruction((SSAGetInstruction) c.original, def, c.ref, c.field);
    }

    public Expression substituteGet(GetInstruction c)
            throws StaticRegionException {
        int defNumber = ((WalaVarExpr)c.def).number;
        final boolean isStatic = ((SSAGetInstruction) c.original).isStatic();
        int objRef;
        if (!isStatic) objRef = ((IntConstant)c.ref).getValue();
        else objRef = -1;
        String fieldName = c.field.getName().toString();
        String className = isStatic ? c.field.getDeclaringClass().getName().getClassName().toString():
                ti.getClassInfo(objRef).getName();
        String exceptionalMessage = null;
        Expression def = null;
        String type = null;
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
                    FieldInfo fieldInfo = null;
                    if (ci != null && !isStatic)
                        fieldInfo = ci.getInstanceField(fieldName);
                    if (ci != null && isStatic)
                        fieldInfo = ci.getStaticField(fieldName);
                    if (fieldInfo == null) {
                        exceptionalMessage = "java.lang.NoSuchFieldError" + "referencing field '" + fieldName
                                + "' in " + eiFieldOwner;
                    } else {
                        gov.nasa.jpf.symbc.numeric.Expression fieldAttr =
                                (gov.nasa.jpf.symbc.numeric.Expression) eiFieldOwner.getFieldAttr(fieldInfo);
                        if (fieldAttr != null) {
                            Expression greenExpr = SPFToGreenExpr(fieldAttr);
                            def = greenExpr;
                        } else {
                            if (fieldInfo.getStorageSize() == 1) {
                                if (fieldInfo.getType() == "float") {
                                    def = new RealConstant(Float.intBitsToFloat(eiFieldOwner.get1SlotField(fieldInfo)));
                                }
                                if (fieldInfo.getType() == "int" || fieldInfo.getType() == "boolean" ||
                                        fieldInfo.getType() == "byte" || fieldInfo.getType() == "char" ||
                                        fieldInfo.getType() == "short")
                                    def = new IntConstant(eiFieldOwner.get1SlotField(fieldInfo));
                            } else {
                                if (fieldInfo.getType() == "double")
                                    def = new RealConstant(Double.longBitsToDouble(eiFieldOwner.get2SlotField(fieldInfo)));
                                if (fieldInfo.getType() == "long")
                                    def = new IntConstant((int) eiFieldOwner.get2SlotField(fieldInfo));
                            }
                            if (def == null) exceptionalMessage = "unsupported field type";
                            else type = fieldInfo.getType();
                        }
                    }
                }
            }
        }
        // if def is non-null, type cannot be null
        assert def == null || type != null;
        // only one of def and exceptionalMessage should be non-null
        assert (def == null) ^ (exceptionalMessage == null);
        valueSymbolTable.add(defNumber, def);
        if (stackSlotTable.lookup(defNumber) != null) {
            slotTypeTable.add(defNumber, type);
        }
        walaNumTypesTable.add(defNumber, type);

        if (exceptionalMessage != null) throw new StaticRegionException(exceptionalMessage);
        if (def != null) return def;
        return null;
    }

}
