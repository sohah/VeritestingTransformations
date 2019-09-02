package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.WholeSpecRepair.synthesis;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil;
import jkind.lustre.*;

import java.util.ArrayList;
import java.util.Objects;

public class PreHoleContainer extends HoleContainer implements Hole, Cloneable {

    //if set indicates that the value of the expression before repair already had a pre in it.
    //for PreContainers that have this bool set, the arraylist of contained holes should be only 1, since we do not
    // need to have initHole for this.
    boolean isOriginalPre = false;

    //this contains the original expression that we are now trying to find repair for.
    Expr originalExpr;

    //an invariant here is that the first element
    public PreHoleContainer(String id, NamedType type, Expr originalExpr, ArrayList<Hole> holes) {
        super(id, type, holes);
        this.originalExpr = originalExpr;
    }


    // Makes a constraint on possible values of the hole depending on the equalityExprValues.
    public Equation getContainerEquation() {
        assert (myHoles.size() == 2);
        Expr rhs = null;
        if ((originalExpr instanceof UnaryExpr) && (((UnaryExpr) originalExpr).op == UnaryOp.PRE)) {
            rhs = new IfThenElseExpr(new IdExpr(myHoles.get(0).toString()),
                    new BinaryExpr((IdExpr) myHoles.get(1), BinaryOp.ARROW, originalExpr), ((UnaryExpr) originalExpr).expr);
        } else {
            rhs = new IfThenElseExpr(new IdExpr(myHoles.get(0).toString()),
                    originalExpr, new BinaryExpr((IdExpr) myHoles.get(1), BinaryOp.ARROW, new UnaryExpr(UnaryOp.PRE,
                    originalExpr)));
        }
        return new Equation(new IdExpr(getContainerName()), rhs);
    }


    public VarDecl getContainerVarDecl() {
        return DiscoveryUtil.IdExprToVarDecl(new IdExpr(getContainerName()), myType);
    }

}
