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
        equationList.addAll(inOutManager.getTypeConversionEq()); // adding type conversion equations.
        localDeclList.addAll(inOutManager.getConversionLocalList());
        equationList.add(addSymVarEquation());
        ArrayList<VarDecl> inputDeclList = inOutManager.generateInputDecl();
        ArrayList<VarDecl> ouputDeclList = inOutManager.generateOutputDecl();
        ArrayList<VarDecl> methodOutDeclList = inOutManager.generaterMethodOutDeclList();
        ouputDeclList.addAll(methodOutDeclList);
        return new Node("R_node", inputDeclList, ouputDeclList, localDeclList, equationList, new ArrayList<>(),
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

    /**
     * used to remove "." and "$" from the text generated to make it type compatible.
     * @param node
     * @return
     */
    public static String lustreFriendlyString(Node node){
        String nodeStr = node.toString();
        nodeStr = nodeStr.replaceAll("\\.", "_");
        nodeStr = nodeStr.replaceAll("\\$", "_");
        return nodeStr;
    }
/*

    */
/**
     * This method attaches a dummy true property to "node"
     * @param node
     * @return
     *//*

    public static Node addDummyTrueProp(Node node){
        node.locals.add(new VarDecl("dummyProp", NamedType.BOOL));
        node.equations.add(new Equation(new IdExpr("dummyProp"), new BoolExpr(true)));
        node.properties.add("dummyProp");
        return node;
    }
*/
}
