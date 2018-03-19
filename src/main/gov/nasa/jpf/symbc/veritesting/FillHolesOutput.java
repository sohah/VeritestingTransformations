package gov.nasa.jpf.symbc.veritesting;

import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Operation;

import java.util.HashMap;
import java.util.LinkedHashMap;

public class FillHolesOutput {
    public LinkedHashMap<Expression, Expression> holeHashMap;
    public Expression additionalAST;
    public FillHolesOutput(LinkedHashMap<Expression, Expression> h, Expression additionalAST) {
        this.holeHashMap = h;
        this.additionalAST = additionalAST;
    }
}
