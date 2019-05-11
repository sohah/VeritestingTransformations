package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.LustreTranslation;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Contract;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.InOutManager;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import jkind.lustre.*;

import java.util.ArrayList;

public class ToLutre {
    public static Node generateRnode(DynamicRegion dynamicRegion, Contract contract){
        InOutManager inOutManager = contract.inOutManager;
        ArrayList<VarDecl> localDeclList = DeclarationTranslator.execute(dynamicRegion, inOutManager);
        localDeclList.add(addSymVar());
        ArrayList<Equation> equationList = EquationVisitor.execute(dynamicRegion);
        equationList.add(addSymVarEquation());
        ArrayList<VarDecl> inputDeclList = inOutManager.generateInputDecl();
        ArrayList<VarDecl> ouputDeclList = inOutManager.generateOutputDecl();
        ArrayList<VarDecl> methodOutDeclList = inOutManager.generaterMethodOutDeclList();
        inputDeclList.addAll(ouputDeclList);
        return new Node("R_node", inputDeclList, methodOutDeclList, localDeclList, equationList, new ArrayList<>(),
                new ArrayList<>(), null, null, null);
    }

    //adding symVar equation, this can be taken out if we do not need symVar wrapper
    private static Equation addSymVarEquation() {
        return new Equation(new IdExpr("symVar"), new IntExpr(1));
    }
    //adding symVar declaration, this can be taken out if we do not need symVar wrapper
    private static VarDecl addSymVar() {
        return new VarDecl("symVar", NamedType.INT);
    }

    //TODO
    public static Node generateRwrapper(){
        System.out.println("not implemented yet!");
        assert false;
        return null;
    }
}
