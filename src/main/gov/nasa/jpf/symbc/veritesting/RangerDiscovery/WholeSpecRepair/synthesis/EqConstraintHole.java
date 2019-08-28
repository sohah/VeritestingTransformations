package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.WholeSpecRepair.synthesis;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil;
import jkind.lustre.*;

import java.util.ArrayList;
import java.util.Objects;

public class EqConstraintHole extends IdExpr implements Hole, Cloneable {
    private static int prefix = 0;
    private static String holeName = "hole";
    private static String helperName = "val";

    public final int myPrefix;


    //this is used to hold possible values
    ArrayList<Expr> equalityExprValues = new ArrayList<>();

    public EqConstraintHole(Location location, String id) {
        super(location, (holeName + "_" + prefix));
        myPrefix = prefix;
        prefix++;
    }

    public EqConstraintHole(String id) {
        super(holeName + "_" + prefix);
        myPrefix = prefix;
        prefix++;
    }

    public static void resetCount() {
        prefix = 0;
    }

    public static int getCurrentHolePrefix() {
        return prefix;
    }

    public static String recreateHoleName(int id) {
        return holeName + "_" + id;
    }

    public String getMyHoleName() {
        return holeName + "_" + myPrefix;
    }

    @Override
    public boolean isEqual(Hole anotherHole) {
        return (this.getMyHoleName().equals(((EqConstraintHole) anotherHole).getMyHoleName()));
    }

    @Override
    public int hashCode() {
        return Objects.hashCode(myPrefix);
    }

    // Makes a constraint on possible values of the hole depending on the equalityExprValues.
    public Expr getHoleConstraint() {
        assert (equalityExprValues.size() > 1);

        Expr rhs = new BinaryExpr(new IdExpr(getMyHoleName()), BinaryOp.EQUAL, equalityExprValues.get(0));

        for (int i = 1; i < equalityExprValues.size(); i++) {
            rhs = new BinaryExpr(rhs, BinaryOp.OR, new BinaryExpr(new IdExpr(getMyHoleName()), BinaryOp.EQUAL, equalityExprValues.get(i)));
        }
        return rhs;

    }


    public Equation getHelperConstraint() {
        assert (equalityExprValues.size() > 1);

        IfThenElseExpr rhs = cascadeHelperIf(0);

        return new Equation(new IdExpr(getHelperName()), rhs);

    }

    private IfThenElseExpr cascadeHelperIf(int i) {
        if (i == equalityExprValues.size() - 2)
            return new IfThenElseExpr(new BinaryExpr(new IdExpr(getMyHoleName()), BinaryOp.EQUAL, equalityExprValues.get(i)), new IntExpr(i), new IntExpr(i + 1));
        else
            return new IfThenElseExpr(new BinaryExpr(new IdExpr(getMyHoleName()), BinaryOp.EQUAL, equalityExprValues.get(i)), new IntExpr(i), cascadeHelperIf(i + 1));
    }

    public void setEqualityExprValues(ArrayList<Expr> equalityExprValues) {
        this.equalityExprValues = equalityExprValues;
    }

    public VarDecl getHelperVarDecl() {
        return DiscoveryUtil.IdExprToVarDecl(new IdExpr(helperName + "_" + myPrefix), NamedType.INT);
    }

    public String getHelperName() {
        return helperName + "_" + myPrefix;
    }
}
