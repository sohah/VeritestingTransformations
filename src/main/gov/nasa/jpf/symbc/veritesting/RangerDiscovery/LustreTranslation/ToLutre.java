package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.LustreTranslation;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.InOutManager;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import jkind.lustre.*;

import java.util.ArrayList;

public class ToLutre {
    public static Node execute(DynamicRegion dynamicRegion, InOutManager inOutManager){
        ArrayList<VarDecl> localDeclList = DeclarationVisitor.execute(dynamicRegion, inOutManager);
        ArrayList<Equation> equationList = EquationVisitor.execute(dynamicRegion, inOutManager);
        ArrayList<VarDecl> inputDeclList = inOutManager.generateInputDecl();
        ArrayList<VarDecl> ouputDeclList = inOutManager.generateOutputDecl();
        return new Node("R_node", inputDeclList, ouputDeclList, localDeclList, equationList, new ArrayList<>(),
                new ArrayList<>(), new ArrayList<>(), null, null);
    }
}
