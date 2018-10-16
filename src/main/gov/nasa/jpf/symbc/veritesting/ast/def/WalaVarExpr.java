package gov.nasa.jpf.symbc.veritesting.ast.def;

import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.Visitor;
import za.ac.sun.cs.green.expr.VisitorException;

import java.util.List;

/**
 * This is the class of Wala Variables in RangerIR.
 */
public final class WalaVarExpr extends Variable {
    /**
     * This number matches the number defined for a specific Wala Variable.
     */
    public final int number;

    public WalaVarExpr(int var) {
        super("@w" + var);
        this.number = var;
    }

    public WalaVarExpr(int var, String name){
        super("@w" + name);
        this.number = var;
    }


    @Override
    public void accept(Visitor visitor) throws VisitorException {
        visitor.preVisit(this);
        visitor.postVisit(this);
    }

    @Override
    public boolean equals(Object o) {
        if (o != null && o instanceof WalaVarExpr) {
            WalaVarExpr other = (WalaVarExpr)o;
            return this.number == other.number;
        }
        return false;
    }


    /**
     * Gets the symbolic name to be used for vars in SPF.
     * @return retrunds symbolic name, which is the name of the WalaVarExpr, without the @ sign
     */
    public String getSymName(){
        return "w"+ Integer.toString(number);
    }

    @Override
    public String toString() {
        return getName();
    }

    @Override
    public int getLength() {
        return 0;
    }

    @Override
    public int getLeftLength() {
        return 0;
    }

    @Override
    public int numVar() {
        return 0;
    }

    @Override
    public int numVarLeft() {
        return 0;
    }

    @Override
    public List<String> getOperationVector() {
        return null;
    }

    public WalaVarExpr clone(){
        String name = getName();
        if (name.startsWith("@w"))
            return new WalaVarExpr(number, name.substring(2));
        else return new WalaVarExpr(number, name);
    }

    public static WalaVarExpr getUniqueWalaVarExpr(WalaVarExpr expr, int uniqueNum) {
        String varId = Integer.toString(expr.number);
        varId = varId.concat("$");
        varId = varId.concat(Integer.toString(uniqueNum));
        return new WalaVarExpr(expr.number, varId);
    }

    @Override
    public int hashCode() {
        return getName().hashCode();
    }
}
