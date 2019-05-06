package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.LustreTranslation;

import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.def.IfThenElseExpr;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitorAdapter;
import ia_parser.Exp;
import jkind.lustre.*;
import jkind.lustre.Ast;
import za.ac.sun.cs.green.expr.*;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Contract.lusterFloatType;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Contract.lusterIntType;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Contract.lusterStringType;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil.stringToLusterType;


public class EquationExprVisitor implements ExprVisitor<jkind.lustre.Ast> {

    DynamicRegion dynRegion;
    ExprVisitorAdapter<Ast> eva;

    public EquationExprVisitor(DynamicRegion dynRegion) {
        this.dynRegion = dynRegion;
        eva = new ExprVisitorAdapter<Ast>(this);
    }

    @Override
    public Ast visit(IntConstant expr) {
        return new IntExpr(expr.getValue());
    }

    @Override
    public Ast visit(IntVariable expr) {
        return new VarDecl(expr.toString(), lusterIntType);
    }

    @Override
    public Ast visit(Operation operation) {
        int operationArity = operation.getArity();
        if (operationArity == 1) {
            Ast lusterOperand = eva.accept(operation.getOperand(0));
            assert (lusterOperand instanceof Expr);
            return new UnaryExpr(UnaryOp.fromString(operation.getOperator().toString()), (Expr) lusterOperand);
        } else if (operationArity == 2) {
            Ast lusterOperand1 = eva.accept(operation.getOperand(0));
            Ast lusterOperand2 = eva.accept(operation.getOperand(1));
            assert (lusterOperand1 instanceof Expr) && (lusterOperand2 instanceof Expr);
            return new BinaryExpr((Expr) lusterOperand1, BinaryOp.fromString(operation.getOperator().toString()), (Expr)
                    lusterOperand2);
        } else {
            System.out.println("unsupported operator arity");
            assert false;
        }

        return null;
    }

    @Override
    public Ast visit(RealConstant expr) {
        System.out.println("Reals are not yet supported");
        assert false;
        return null;
    }

    @Override
    public Ast visit(RealVariable expr) {
        return new VarDecl(expr.toString(), lusterFloatType);

    }

    @Override
    public Ast visit(StringConstantGreen expr) {//TODO
        System.out.println("Strings are not yet supported");
        assert false;
        return null;
    }

    @Override
    public Ast visit(StringVariable expr) {
        return new VarDecl(expr.toString(), lusterStringType);
    }

    @Override
    public Ast visit(IfThenElseExpr expr) {
        Ast lusterCondition = eva.accept(expr.condition);
        assert (lusterCondition instanceof Expr);

        Ast lusterThenExpr = eva.accept(expr.thenExpr);
        assert (lusterThenExpr instanceof Expr);

        Ast lusterElseExpr = eva.accept(expr.elseExpr);
        assert (lusterElseExpr instanceof Expr);

        jkind.lustre.IfThenElseExpr lustreIfThenElse = new jkind.lustre.IfThenElseExpr((Expr) lusterCondition, (Expr) lusterThenExpr, (Expr) lusterElseExpr);

        return lustreIfThenElse;
    }

    @Override
    public Ast visit(ArrayRefVarExpr expr) {//TODO
        System.out.println("Arrays are not yet supported");
        assert false;
        return null;
    }

    @Override
    public Ast visit(WalaVarExpr expr) {
        String type = (String) dynRegion.varTypeTable.lookupByName(expr.toString());
        assert (type != null);
        return new VarDecl(expr.toString(), stringToLusterType(type));
    }

    @Override
    public Ast visit(FieldRefVarExpr expr) {
        String type = dynRegion.fieldRefTypeTable.lookup(expr);
        assert (type != null);
        return new VarDecl(expr.toString(), stringToLusterType(type));
    }

    @Override
    public Ast visit(GammaVarExpr expr) {
        Ast lusterCondition = eva.accept(expr.condition);
        assert (lusterCondition instanceof Expr);

        Ast lusterThenExpr = eva.accept(expr.thenExpr);
        assert (lusterThenExpr instanceof Expr);

        Ast lusterElseExpr = eva.accept(expr.elseExpr);
        assert (lusterElseExpr instanceof Expr);

        jkind.lustre.IfThenElseExpr lustreIfThenElse = new jkind.lustre.IfThenElseExpr((Expr) lusterCondition, (Expr) lusterThenExpr, (Expr) lusterElseExpr);

        return lustreIfThenElse;
    }

    @Override
    public Ast visit(AstVarExpr expr) {//TODO
        System.out.println("return vars are not yet supported");
        assert false;
        return null;
    }
}
