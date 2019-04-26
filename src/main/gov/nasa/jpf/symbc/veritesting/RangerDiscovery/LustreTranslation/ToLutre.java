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
        ArrayList<Equation> equationList = EquationVisitor.execute(dynamicRegion, inOutManager);
        ArrayList<VarDecl> inputDeclList = inOutManager.generateInputDecl();
        ArrayList<VarDecl> ouputDeclList = inOutManager.generateOutputDecl();
        return new Node("R_node", inputDeclList, ouputDeclList, localDeclList, equationList, new ArrayList<>(),
                new ArrayList<>(), new ArrayList<>(), null, null);
    }

    //TODO
    public static Node generateRwrapper(){
        System.out.println("not implemented yet!");
        assert false;
        return null;
    }
}
