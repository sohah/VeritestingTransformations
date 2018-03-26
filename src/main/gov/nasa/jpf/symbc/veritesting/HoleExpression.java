package gov.nasa.jpf.symbc.veritesting;

import com.ibm.wala.types.TypeReference;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Visitor;
import za.ac.sun.cs.green.expr.VisitorException;

import java.lang.reflect.Array;
import java.util.List;

public class HoleExpression extends za.ac.sun.cs.green.expr.Expression{
    public boolean isLatestWrite = true;
    private int globalStackSlot = -1;

    @Override
    public void accept(Visitor visitor) throws VisitorException {
        visitor.preVisit(this);
        visitor.postVisit(this);
    }

    @Override
    public boolean equals(Object object) {
        if(object instanceof HoleExpression) {
            HoleExpression holeExpression = (HoleExpression) object;
            if(holeExpression.getHoleType() != holeType) return false;
            if(!holeExpression.getHoleVarName().equals(holeVarName))
                return false;
            switch(holeExpression.getHoleType()) {
                case LOCAL_INPUT:
                case LOCAL_OUTPUT:
                    if(holeExpression.getLocalStackSlot() != localStackSlot)
                        return false;
                    else return true;
                case INTERMEDIATE:
                    return true;
                case NONE:
                    return true;
                case CONDITION:
                    return true;
                case NEGCONDITION:
                    return true;
                case FIELD_INPUT:
                case FIELD_OUTPUT:
                    FieldInfo fieldInfo1 = holeExpression.getFieldInfo();
                    if(!fieldInfo1.className.equals(fieldInfo.className) ||
                            !fieldInfo1.fieldName.equals(fieldInfo.fieldName) ||
                            fieldInfo1.localStackSlot != fieldInfo.localStackSlot ||
                            fieldInfo1.callSiteStackSlot != fieldInfo.callSiteStackSlot ||
                            (fieldInfo1.writeValue != null && fieldInfo.writeValue != null && !fieldInfo1.writeValue.equals(fieldInfo.writeValue)))
                        return false;
                    else return true;
                case INVOKE:
                    InvokeInfo otherInvokeInfo = holeExpression.invokeInfo;
                    return (!otherInvokeInfo.equals(invokeInfo));
            }
            return true;
        }
        else return false;
    }

    @Override
    public String toString() {
        String ret = new String();
        ret += "(type = " + holeType + ", name = " + holeVarName;
        switch (holeType) {
            case LOCAL_INPUT:
            case LOCAL_OUTPUT:
                ret += ", stackSlot = " + localStackSlot;
                break;
            case INTERMEDIATE:
                break;
            case NONE:
                break;
            case CONDITION:
                break;
            case NEGCONDITION:
                break;
            case FIELD_INPUT:
            case FIELD_OUTPUT:
                ret += ", fieldInfo = " + fieldInfo.toString();
                break;
            case INVOKE:
                ret += ", invokeInfo = " + invokeInfo.toString();
                break;
            case ARRAYLOAD:
                ret += ", arrayInfo = " + arrayInfoHole.toString();
                break;
            default:
                System.out.println("undefined toString for holeType (" + holeType + ")");
                assert(false);
        }
        ret += ")";
        return ret;
    }

    @Override
    public int getLength() {
        return 1;
    }

    @Override
    public int getLeftLength() {
        return 1;
    }

    @Override
    public int numVar() {
        return 1;
    }

    @Override
    public int numVarLeft() {
        return 1;
    }

    @Override
    public List<String> getOperationVector() {
        return null;
    }

    final long holeID;
    HoleExpression(long _holeID) { holeID = _holeID; }

    public void setHoleVarName(String holeVarName) {
        this.holeVarName = holeVarName;
    }
    public String getHoleVarName() {
        return holeVarName;
    }
    String holeVarName = "";

    public void setGlobalStackSlot(int globalStackSlot) {
        assert(localStackSlot != -1);
        assert(holeType == HoleType.LOCAL_INPUT || holeType == HoleType.LOCAL_OUTPUT);
        this.globalStackSlot = globalStackSlot;
    }

    public int getStackSlot() {
        assert(localStackSlot != -1);
        assert(holeType == HoleType.LOCAL_INPUT || holeType == HoleType.LOCAL_OUTPUT);
        if(globalStackSlot != -1) return globalStackSlot;
        else return getLocalStackSlot();
    }

    public static boolean isLocal(Expression expression) {
        if(!(expression instanceof HoleExpression)) return false;
        HoleExpression h = (HoleExpression) expression;
        return (h.holeType == HoleType.LOCAL_OUTPUT || h.holeType == HoleType.LOCAL_INPUT);
    }

    public enum HoleType {
        LOCAL_INPUT("local_input"),
        LOCAL_OUTPUT("local_output"),
        INTERMEDIATE("intermediate"),
        NONE ("none"),
        CONDITION("condition"),
        NEGCONDITION("negcondition"),
        FIELD_INPUT("field_input"),
        FIELD_OUTPUT("field_output"),
        INVOKE("invoke"),
        ARRAYLOAD("array_load");
        private final String string;

        HoleType(String string) {
            this.string = string;
        }
    }

    public HoleType getHoleType() {
        return holeType;
    }

    HoleType holeType = HoleType.NONE;

    public boolean isHole() {
        return isHole;
    }

    public void setHole(boolean hole, HoleType h) {
        isHole = hole; holeType = h;
        assert((isHole && holeType == HoleType.LOCAL_INPUT) ||
                (isHole && holeType == HoleType.LOCAL_OUTPUT) ||
                (isHole && holeType == HoleType.INTERMEDIATE) ||
                (isHole && holeType == HoleType.CONDITION) ||
                (isHole && holeType == HoleType.NEGCONDITION) ||
                (isHole && holeType == HoleType.FIELD_INPUT) ||
                (isHole && holeType == HoleType.FIELD_OUTPUT) ||
                (isHole && holeType == HoleType.INVOKE) ||
                (isHole && holeType == HoleType.ARRAYLOAD) ||
                (!isHole && holeType == HoleType.NONE));
    }

    protected boolean isHole = false;

    public void setLocalStackSlot(int localStackSlot) {
        assert(holeType == HoleType.LOCAL_INPUT || holeType == HoleType.LOCAL_OUTPUT);
        if(localStackSlot == -1) {
            System.out.println("Hole " + toString() + " cannot be given new stack slot (" + localStackSlot + ")");
            assert(false);
        }
        this.localStackSlot = localStackSlot;
    }
    public int getLocalStackSlot() {
        assert(holeType == HoleType.LOCAL_INPUT || holeType == HoleType.LOCAL_OUTPUT);
        return localStackSlot;
    }
    protected int localStackSlot = -1;

    public void setFieldInfo(String className, String fieldName, int localStackSlot, int callSiteStackSlot,
                             Expression writeExpr, boolean isStaticField, HoleExpression useHole) {
        assert(holeType == HoleType.FIELD_INPUT || holeType == HoleType.FIELD_OUTPUT);
        //the object reference should either be local, come from another hole, or this field should be static
        assert((localStackSlot != -1 || callSiteStackSlot != -1) || (useHole != null) || isStaticField);
        if(holeType == HoleType.FIELD_OUTPUT) {
            assert (writeExpr != null);
            assert (writeExpr instanceof HoleExpression);
            assert (((HoleExpression)writeExpr).getHoleType() == HoleType.INTERMEDIATE);
        }
        if(holeType == HoleType.FIELD_INPUT) assert(writeExpr == null);
        fieldInfo = new FieldInfo(className, fieldName, localStackSlot, callSiteStackSlot, writeExpr, isStaticField, useHole);
    }

    public FieldInfo getFieldInfo() {
        return fieldInfo;
    }

    public ArrayInfoHole getArrayInfo() { return arrayInfoHole; }
    public void setArrayInfo(Expression arrayRef, Expression arrayIndex, TypeReference arrayType, String pathLabelString, int pathLabel) {
        assert(this.isHole && this.holeType == HoleType.ARRAYLOAD);
        arrayInfoHole = new ArrayInfoHole(arrayRef, arrayIndex, arrayType, pathLabelString, pathLabel);
    }
    ArrayInfoHole arrayInfoHole = null;

    public class ArrayInfoHole{
        public Expression arrayRefHole,arrayIndexHole;
        public TypeReference arrayType;
        String pathLabelString;
        int pathLabel;

        public ArrayInfoHole(Expression arrayRef, Expression arrayIndex, TypeReference arrayType, String pathLabelString, int pathLabel){
            this.arrayRefHole = arrayRef;
            this.arrayIndexHole = arrayIndex;
            this.arrayType = arrayType;
            this.pathLabelString = pathLabelString;
            this.pathLabel = pathLabel;
        }

        public String getPathLabelString() {
            return pathLabelString;
        }

        public int getPathLabel() {
            return pathLabel;
        }

        @Override
        public String toString() {
            return arrayRefHole + "[" + arrayType +":" +arrayIndexHole + "]";
        }

        public boolean equals(Object o) {
            if(!(o instanceof ArrayInfoHole)) return false;
            ArrayInfoHole arrayInfoHole = (ArrayInfoHole) o;
            if(arrayInfoHole.arrayIndexHole != (this.arrayIndexHole) ||
                    arrayInfoHole.arrayType != (this.arrayType) ||
                    arrayInfoHole.arrayRefHole != (this.arrayRefHole) )
                return false;
            else return true;
        }
    }

    public class FieldInfo {
        public String className, fieldName;
        public int localStackSlot = -1, callSiteStackSlot = -1;
        public Expression writeValue = null;
        public boolean isStaticField = false;
        public HoleExpression useHole = null;

        public FieldInfo(String className, String fieldName, int localStackSlot, int callSiteStackSlot,
                         Expression writeValue, boolean isStaticField, HoleExpression useHole) {
            this.localStackSlot = localStackSlot;
            this.callSiteStackSlot = callSiteStackSlot;
            this.className = className;
            this.fieldName = fieldName;
            this.writeValue = writeValue;
            this.isStaticField = isStaticField;
            this.useHole = useHole;
        }

        public String toString() {
            String ret = "currentClassName = " + className + ", fieldName = " + fieldName +
                    ", stackSlots (local = " + localStackSlot + ", callSite = " + callSiteStackSlot;
            if(writeValue != null) ret += ", writeValue (" + writeValue.toString() + ")";
            else ret += ")";
            ret += ", isStaticField = " + isStaticField;
            return ret;
        }

        public boolean equals(Object o) {
            if(!(o instanceof FieldInfo)) return false;
            FieldInfo fieldInfo1 = (FieldInfo) o;
            if(!fieldInfo1.className.equals(this.className) ||
                    !fieldInfo1.fieldName.equals(this.fieldName) ||
                    fieldInfo1.localStackSlot != this.localStackSlot ||
                    fieldInfo1.callSiteStackSlot != this.callSiteStackSlot ||
                    (fieldInfo1.writeValue != null && this.writeValue != null && !fieldInfo1.writeValue.equals(this.writeValue)))
                return false;
            else return true;
        }
    }

    FieldInfo fieldInfo = null;

    public void setInvokeInfo(InvokeInfo invokeInfo) {
        this.invokeInfo = invokeInfo;
    }
    public InvokeInfo getInvokeInfo() {
        return invokeInfo;
    }
    InvokeInfo invokeInfo = null;

    public Expression dependsOn = null;
}
