package gov.nasa.jpf.symbc.veritesting.ast.transformations.fieldaccess;

import com.ibm.wala.ssa.SSAGetInstruction;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.GetInstruction;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution.ValueSymbolTable;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.vm.*;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.RealConstant;


import java.util.HashSet;

import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.SPFToGreenExpr;

public class GetSubstitutionVisitor extends AstMapVisitor {
    private ValueSymbolTable valueSymbolTable;
    private ThreadInfo ti;
    public GetSubstitutionVisitor(ThreadInfo ti, ValueSymbolTable valueSymbolTable) {
        super(new ExprMapVisitor());
        this.ti = ti;
        this.valueSymbolTable = valueSymbolTable;
    }

    public static DynamicRegion doSubstitution(ThreadInfo ti, DynamicRegion dynRegion) {
        GetSubstitutionVisitor visitor = new GetSubstitutionVisitor(ti,
                dynRegion.valueSymbolTable);
        Stmt dynStmt = dynRegion.dynStmt.accept(visitor);
        return new DynamicRegion(dynRegion.staticRegion, dynStmt, dynRegion.slotTypeTable, visitor.valueSymbolTable, new HashSet<>());
    }

    @Override
    public Stmt visit(GetInstruction c) {
        // If we are doing a get field from a constant object reference or if this field access is a static access,
        // we can fill this input in
        if (c.ref instanceof IntConstant || ((SSAGetInstruction)c.original).isStatic()) {
            Expression def;
            try {
                if (!(c.def instanceof WalaVarExpr))
                    throw new StaticRegionException("def not instance of WalaVarExpr in GetInstruction: " + c);
                else {
                    int number = ((WalaVarExpr)c.def).number;
                    def = substituteGet(c);
                    valueSymbolTable.add(number, def);
                }
            } catch (StaticRegionException e) {
                System.out.println("Failed to substitute input for GetInstruction: " + c);
                throw new IllegalArgumentException(e.getMessage());
            }
            return new GetInstruction((SSAGetInstruction) c.original, def, c.ref, c.field);
        }
        return super.visit(c);
    }

    public Expression substituteGet(GetInstruction c)
            throws StaticRegionException {

        final boolean isStatic = ((SSAGetInstruction) c.original).isStatic();
        int objRef;
        if (!isStatic) objRef = ((IntConstant)c.ref).getValue();
        else objRef = -1;
        String fieldName = c.field.getName().toString();
        String className = isStatic ? c.field.getDeclaringClass().getName().getClassName().toString(): ti.getClassInfo(objRef).getName();
        if (objRef == 0) {
            System.out.println("java.lang.NullPointerException" + "referencing field '" +
                    fieldName + "' on null object");
            assert (false);
        } else {
            ClassInfo ci;
            try {
                ci = ClassLoaderInfo.getCurrentResolvedClassInfo(className);
            } catch (ClassInfoException e) {
                throw new StaticRegionException("fillFieldInputHole: class loader failed to resolve class name " +
                        className);
            }
            ElementInfo eiFieldOwner;
            if (!isStatic)
                eiFieldOwner = ti.getElementInfo(objRef);
            else
                eiFieldOwner = ci.getStaticElementInfo();
            if (eiFieldOwner == null) throw new StaticRegionException("failed to resolve eiFieldOwner for field");
            FieldInfo fieldInfo = null;
            if (ci != null && !isStatic)
                fieldInfo = ci.getInstanceField(fieldName);
            if (ci != null && isStatic)
                fieldInfo = ci.getStaticField(fieldName);
            if (fieldInfo == null) {
                System.out.println("java.lang.NoSuchFieldError" + "referencing field '" + fieldName
                        + "' in " + eiFieldOwner);
                assert (false);
            } else {
                gov.nasa.jpf.symbc.numeric.Expression fieldAttr =
                        (gov.nasa.jpf.symbc.numeric.Expression) eiFieldOwner.getFieldAttr(fieldInfo);
                if (fieldAttr != null) {
                    Expression greenExpr = SPFToGreenExpr(fieldAttr);
                    return greenExpr;
                } else {
                    if (fieldInfo.getStorageSize() == 1) {
                        if (fieldInfo.getType() == "float")
                            return new RealConstant(Float.intBitsToFloat(eiFieldOwner.get1SlotField(fieldInfo)));
                        if (fieldInfo.getType() == "int" || fieldInfo.getType() == "boolean" ||
                                fieldInfo.getType() == "byte" || fieldInfo.getType() == "char" ||
                                fieldInfo.getType() == "short")
                            return new IntConstant(eiFieldOwner.get1SlotField(fieldInfo));
                    } else {
                        if (fieldInfo.getType() == "double")
                            return new RealConstant(Double.longBitsToDouble(eiFieldOwner.get2SlotField(fieldInfo)));
                        if (fieldInfo.getType() == "long")
                            return new IntConstant((int) eiFieldOwner.get2SlotField(fieldInfo));

                    }
                    throw new StaticRegionException("unsupported field type");
                }
            }
        }
        return null;
    }

}
