package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.LustreTranslation;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.InOutManager;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import jkind.lustre.Ast;
import jkind.lustre.VarDecl;

import java.util.ArrayList;

public class DeclarationVisitor implements AstVisitor<Ast> {

    private final DynamicRegion dynamicRegion;
    private final InOutManager inOutManager;
    private ArrayList<Ast> declarationList;

    public DeclarationVisitor(DynamicRegion dynamicRegion, InOutManager inOutManager) {
        this.dynamicRegion = dynamicRegion;
        this.inOutManager = inOutManager;
    }

    @Override
    public Ast visit(AssignmentStmt a) {
        return null;
    }

    @Override
    public Ast visit(CompositionStmt a) {
        return null;
    }

    @Override
    public Ast visit(IfThenElseStmt a) {
        return null;
    }

    @Override
    public Ast visit(SkipStmt a) {
        return null;
    }

    @Override
    public Ast visit(SPFCaseStmt c) {
        return null;
    }

    @Override
    public Ast visit(ArrayLoadInstruction c) {
        return null;
    }

    @Override
    public Ast visit(ArrayStoreInstruction c) {
        return null;
    }

    @Override
    public Ast visit(SwitchInstruction c) {
        return null;
    }

    @Override
    public Ast visit(ReturnInstruction c) {
        return null;
    }

    @Override
    public Ast visit(GetInstruction c) {
        return null;
    }

    @Override
    public Ast visit(PutInstruction c) {
        return null;
    }

    @Override
    public Ast visit(NewInstruction c) {
        return null;
    }

    @Override
    public Ast visit(InvokeInstruction c) {
        return null;
    }

    @Override
    public Ast visit(ArrayLengthInstruction c) {
        return null;
    }

    @Override
    public Ast visit(ThrowInstruction c) {
        return null;
    }

    @Override
    public Ast visit(CheckCastInstruction c) {
        return null;
    }

    @Override
    public Ast visit(InstanceOfInstruction c) {
        return null;
    }

    @Override
    public Ast visit(PhiInstruction c) {
        return null;
    }

    public static ArrayList<VarDecl> execute(DynamicRegion dynamicRegion, InOutManager inOutManager){
        DeclarationVisitor declarationVisitor = new DeclarationVisitor(dynamicRegion, inOutManager);
        dynamicRegion.dynStmt.accept(declarationVisitor);
        return declarationVisitor.declarationList;
    }
}
