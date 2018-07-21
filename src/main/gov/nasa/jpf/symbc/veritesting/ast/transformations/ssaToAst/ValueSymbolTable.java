package gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst;

import com.ibm.wala.ssa.IR;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import za.ac.sun.cs.green.expr.Expression;

import java.util.HashMap;

//SH: all values stored here should be in the form of a green expression

public class ValueSymbolTable {

    private HashMap<Integer, Expression> symbolTable;
    public IR ir;

    public ValueSymbolTable(IR ir) {
        this.ir = ir;
        symbolTable = new HashMap<>();
    }

    public Expression lookup(Integer var) {
        if (var != null)
            return symbolTable.get(var);
        else
            try {
                throw new StaticRegionException("Cannot lookup the value of a null variable.");
            } catch (StaticRegionException e) {
                System.out.println(e.getMessage());
            }
        return null;
    }

    public void add(Integer var, Expression expr) {
        if ((var != null) && (expr != null))
            symbolTable.put(var, expr);
    }

    public void printSymbolTable() {
        System.out.println("\nprinting value symbol table");
        symbolTable.forEach((var, expr) -> System.out.println(var + " --------- " + expr));
    }
}
