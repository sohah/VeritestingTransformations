package gov.nasa.jpf.symbc.veritesting.ast.transformations.fieldaccess;

import gov.nasa.jpf.symbc.veritesting.ast.def.FieldRef;
import gov.nasa.jpf.vm.*;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.RealConstant;

import java.util.Objects;

import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.SPFToGreenExpr;

public class SubstituteGetOutput {
    public FieldRef fieldRef;
    public String exceptionalMessage;
    public Expression def;
    public String type = null;
    private boolean isRead;
    private ThreadInfo ti;
    private gov.nasa.jpf.symbc.numeric.Expression finalValue;

    public SubstituteGetOutput(ThreadInfo ti, FieldRef fieldRef, boolean isRead, gov.nasa.jpf.symbc.numeric.Expression finalValue) {
        this.fieldRef = fieldRef;
        this.isRead = isRead;
        this.ti = ti;
        this.finalValue = finalValue;
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
                if (!isStatic) {
                    if (isRead) eiFieldOwner = ti.getElementInfo(objRef);
                    else eiFieldOwner = ti.getModifiableElementInfo(objRef);
                }
                else {
                    if(isRead) eiFieldOwner = ci.getStaticElementInfo();
                    else eiFieldOwner = ci.getModifiableStaticElementInfo();
                }
                if (eiFieldOwner == null) exceptionalMessage = "failed to resolve eiFieldOwner for field";
                else {
                    FieldInfo fieldInfo;
                    if (!isStatic) fieldInfo = ci.getInstanceField(fieldName);
                    else fieldInfo = ci.getStaticField(fieldName);
                    if (fieldInfo == null) {
                        exceptionalMessage = "java.lang.NoSuchFieldError" + "referencing field '" + fieldName
                                + "' in " + eiFieldOwner;
                    } else {
                        if (isRead) executeRead(eiFieldOwner, fieldInfo);
                        else executeWrite(eiFieldOwner, fieldInfo);
                    }
                }
            }
        }
        return this;
    }

    private void executeWrite(ElementInfo eiFieldOwner, FieldInfo fieldInfo) {
        int fieldSize = fieldInfo.getStorageSize();
        if (fieldSize == 1) {
            eiFieldOwner.set1SlotField(fieldInfo, 0); // field value should not matter (I, Vaibhav, think)
            eiFieldOwner.setFieldAttr(fieldInfo, finalValue);
        } else {
            eiFieldOwner.set2SlotField(fieldInfo, 0); // field value should not matter (I, Vaibhav, think)
            eiFieldOwner.setFieldAttr(fieldInfo, finalValue);
        }
    }

    private void executeRead(ElementInfo eiFieldOwner, FieldInfo fieldInfo) {
        gov.nasa.jpf.symbc.numeric.Expression fieldAttr =
                (gov.nasa.jpf.symbc.numeric.Expression) eiFieldOwner.getFieldAttr(fieldInfo);
        if (fieldAttr != null) {
            def = SPFToGreenExpr(fieldAttr);
            type = fieldInfo.getType();
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