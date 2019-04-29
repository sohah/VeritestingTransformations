package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.LustreTranslation;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.InOutManager;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitorAdapter;
import jkind.lustre.*;
import jkind.lustre.Ast;

import java.util.ArrayList;

public class EquationVisitor extends ExprMapVisitor implements AstVisitor<Ast> {

    protected final ExprVisitor<Ast> exprVisitor;
    protected final ExprVisitorAdapter<Ast> eva;
    private final InOutManager rInOutManager;
    private ArrayList<Equation> equationList = new ArrayList<>();


    private EquationVisitor(ExprVisitor<Ast> exprVisitor, InOutManager rInOutManager) {
        this.rInOutManager = rInOutManager;
        this.eva = new ExprVisitorAdapter<Ast>(exprVisitor);
        this.exprVisitor = exprVisitor;
    }

    @Override
    public Ast visit(AssignmentStmt a) {
        Ast rhs = eva.accept(a.rhs);
        IdExpr lhs = new IdExpr(a.lhs.toString());
        if ((rInOutManager.isContractOutputStr(lhs.id)) && (!rInOutManager.isOutputConverted()))
            equationList.add(addMethodReturnInit(new Equation(lhs, (Expr) rhs)));
        else if ((rInOutManager.isStateOutVar(lhs.id)) && (!rInOutManager.isOutputConverted()))
            equationList.add(addStateOutInit(new Equation(lhs, (Expr) rhs)));
        else
            equationList.add(new Equation(lhs, (Expr) rhs));
        return null;
    }

    /**
     * adds an initial value to the equation if it is the equation of the method output.
     *
     * @param equation
     * @return
     */
    private Equation addMethodReturnInit(Equation equation) {
        IdExpr lhs = equation.lhs.get(0);
        if (rInOutManager.isContractOutputStr(lhs.id)) //if it is a method retrun equation, then proceed it with the initial value
            return DiscoveryUtil.addInitToEq(equation, rInOutManager.getContractOutputInit(lhs.id));

        assert false; //there must be an init value for a method output
        return null;
    }


    private Equation addStateOutInit(Equation equation) {
        IdExpr lhs = equation.lhs.get(0);
        if (rInOutManager.isStateOutVar(lhs.id)) //if it is state output, then proceed it with the initial value
            return DiscoveryUtil.addInitToEq(equation, rInOutManager.getStateOutInit(lhs.id));

        assert false; //there must be an init value for a state output
        return null;
    }


    @Override
    public Ast visit(CompositionStmt a) {
        a.s1.accept(this);
        a.s2.accept(this);
        return null;
    }


    @Override
    public Ast visit(IfThenElseStmt a) {
        assert false;
        return null;
    }

    @Override
    public Ast visit(SkipStmt a) {
        return null;
    }

    @Override
    public Ast visit(SPFCaseStmt c) {
        assert false;
        return null;
    }

    @Override
    public Ast visit(ArrayLoadInstruction c) {
        assert false;
        return null;
    }

    @Override
    public Ast visit(ArrayStoreInstruction c) {
        assert false;
        return null;
    }

    @Override
    public Ast visit(SwitchInstruction c) {
        assert false;
        return null;
    }

    @Override
    public Ast visit(ReturnInstruction c) {
        assert false;
        return null;
    }

    @Override
    public Ast visit(GetInstruction c) {
        assert false;
        return null;
    }

    @Override
    public Ast visit(PutInstruction c) {
        assert false;
        return null;
    }

    @Override
    public Ast visit(NewInstruction c) {
        assert false;
        return null;
    }

    @Override
    public Ast visit(InvokeInstruction c) {
        assert false;
        return null;
    }

    @Override
    public Ast visit(ArrayLengthInstruction c) {
        assert false;
        return null;
    }

    @Override
    public Ast visit(ThrowInstruction c) {
        assert false;
        return null;
    }

    @Override
    public Ast visit(CheckCastInstruction c) {
        assert false;
        return null;
    }

    @Override
    public Ast visit(InstanceOfInstruction c) {
        assert false;
        return null;
    }

    @Override
    public Ast visit(PhiInstruction c) {
        assert false;
        return null;
    }

    public static ArrayList<Equation> execute(DynamicRegion dynRegion, InOutManager rInOutManager) {
        EquationExprVisitor equationExprVisitor = new EquationExprVisitor(dynRegion);
        EquationVisitor equationVisitor = new EquationVisitor(equationExprVisitor, rInOutManager);
        dynRegion.dynStmt.accept(equationVisitor);
        return equationVisitor.equationList;
    }
}
