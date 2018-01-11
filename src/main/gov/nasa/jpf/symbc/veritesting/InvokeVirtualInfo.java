package gov.nasa.jpf.symbc.veritesting;

import za.ac.sun.cs.green.expr.Expression;

import java.util.ArrayList;

public class InvokeVirtualInfo {

    public String className;
    public void setClassName(String className) {
        this.className = className;
    }

    public String methodName;
    public void setMethodName(String methodName) {
        this.methodName = methodName;
    }

    public ArrayList<Expression> paramList;
    public void setParamList(ArrayList<Expression> paramList) {
        this.paramList = paramList;
    }

    public String toString() {
        String ret = new String("");
        ret += "currentClassName = " + className + ", methodName = " + methodName + ", defVal = " + defVal;
        ret += ", paramList = " + paramList.toString();
        return ret;
    }

    public boolean equals(Object o) {
        if(!(o instanceof InvokeVirtualInfo)) return false;
        InvokeVirtualInfo i1 = (InvokeVirtualInfo) o;
        if(!i1.className.equals(className)) return false;
        if(!i1.methodName.equals(methodName)) return false;
        if(!i1.paramList.equals(paramList)) return false;
        return true;
    }

    public void setDefVal(int defVal) {
        this.defVal = defVal;
    }
    public int defVal = -1;
}
