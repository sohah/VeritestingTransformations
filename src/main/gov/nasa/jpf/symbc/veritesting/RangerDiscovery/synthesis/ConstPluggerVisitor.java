package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.synthesis;

import jkind.lustre.*;
import jkind.lustre.values.BooleanValue;
import jkind.lustre.values.IntegerValue;
import jkind.lustre.values.Value;
import jkind.lustre.visitors.AstMapVisitor;

import java.util.HashMap;

/**
 * This visitor puts back the values of the holes into the specification of T.
 */

public class ConstPluggerVisitor extends AstMapVisitor {
    HashMap<Hole, Value> holeSynValuesMap;


    public ConstPluggerVisitor(HashMap<Hole, Value> holeSynValuesMap) {
        this.holeSynValuesMap = holeSynValuesMap;
    }

    @Override
    public Expr visit(IdExpr e) {
        if (e instanceof ConstantHole) {
            Value value = holeSynValuesMap.get(e);
            return translateValueToExpr(value);
        } else
            return e;
    }

    private Expr translateValueToExpr(Value value) {
        if(value instanceof BooleanValue)
            return new BoolExpr(((BooleanValue) value).value);
        else if(value instanceof IntegerValue)
            return new IntExpr(((IntegerValue) value).value);
        else{
            System.out.println("unsupported values type");
            assert false;
            return null;
        }
    }

    public static Ast execute(HashMap<Hole, Value> holeSynValuesMap, Program program){
        ConstPluggerVisitor constPluggerVisitor = new ConstPluggerVisitor(holeSynValuesMap);
        Ast newProgram = program.accept(constPluggerVisitor);
        return newProgram;
    }

}
