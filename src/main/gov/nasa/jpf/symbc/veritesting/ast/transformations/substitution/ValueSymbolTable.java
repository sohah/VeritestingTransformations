package gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution;

import com.ibm.wala.ssa.IR;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import za.ac.sun.cs.green.expr.Expression;

import java.util.HashMap;

//SH: all values stored here should be in the form of a green expression

public class ValueSymbolTable extends Table<Expression> {

    public IR ir;


    public ValueSymbolTable(IR ir) {
        super("var-value table", "var", "value");
        this.ir = ir;
    }
}
