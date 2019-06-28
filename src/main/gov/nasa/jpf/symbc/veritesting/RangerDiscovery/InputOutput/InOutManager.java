package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import jkind.lustre.*;

import java.util.ArrayList;
import java.util.Collection;


/**
 * this class manages the input and output of RNode, it assumes that the input and the output of the "step" function is
 * provided, it is divided into 4 types, freeInput, stateInput, stateOutput and methodOutput. The type of those
 * should match the signature of the step function. Type conversion is needed sometimes, if so then the variable
 * names in the arraylist will change to the new var being created, in this case there will be as well a side effect
 * for the equations needed for conversion between the original var and the new var being created for conversion.
 * <p>
 * An important thing to note here is that the signature of the different input, output, or state are reflecting those
 * in the implementation type.
 */
public class InOutManager {

    //for now we are adding the reference object by hand, it changes from lunix to mac, so I am adding this here to avoid having to repeatedly change the code
    //private String referenceObjectName = "r351"; //for lunix

    private String referenceObjectName = "r347"; //for mac

    Input freeInput = new Input();
    Input stateInput = new Input();
    Output stateOutput = new Output();
    MethodOutput methodOutput = new MethodOutput();

    // carries the output equation of the method, which includes the initial value in case that the output does have an initial value in its related state
    ArrayList<Equation> methodOutEq = new ArrayList<>();

    //carries any type conversion equation which can be triggered both in case of the input and the output
    ArrayList<Equation> typeConversionEq = new ArrayList<>();

    ArrayList<VarDecl> conversionLocalList = new ArrayList<>();
    private Expr methodReturnInit;

    public ArrayList<Equation> getTypeConversionEq() {
        return typeConversionEq;
    }

    public ArrayList<VarDecl> getConversionLocalList() {
        return conversionLocalList;
    }

    public void discoverVars() {
        if (Config.spec.equals("pad")) {
            discoverFreeInputPad();
            discoverStateInputPad();
            discoverStateOutputPad();
            discoverMethodOutputPad();
        } else if (Config.spec.equals("even")) {
            discoverFreeInputEven();
            discoverStateInputEven();
            discoverStateOutputEven();
            discoverMethodOutputEven();
        } else {
            System.out.println("unexpected spec to run.!");
        }
    }

    //entered by hand for now -- this is a singleton, I need to enforce this everywhere.
    private void discoverMethodOutputPad() {
        methodOutput.add(referenceObjectName + ".ignition_r.1.7.4", NamedType.BOOL);
        methodOutput.addInit(referenceObjectName + ".ignition_r.1.7.4", new BoolExpr(false));
        if (methodOutput.containsBool()) { // isn't that replicated with the state output.
            assert methodOutput.size == 1; // a method can only have a single output
            ArrayList<Equation> conversionResult = methodOutput.convertOutput();
            //typeConversionEq.addAll(conversionResult);
            assert conversionResult.size() == 1;
            Equation outputEq = methodOutput.addInitToEq(conversionResult.get(0));
            methodOutEq.add(outputEq); //this creates a proceeded value for the initial value
        } else
            methodOutEq.add(methodOutput.makeInitEq()); // this creates the initial value in case there is no type conversion needed
        //conversionLocalList.addAll(conversionResult.getFirst()); // no need to add this, since these are already as
        // def in the dynStmt
    }

    //entered by hand for now
    private void discoverFreeInputPad() {
        freeInput.add("signal", NamedType.INT);
        if (freeInput.containsBool()) {
            Pair<ArrayList<VarDecl>, ArrayList<Equation>> conversionResult = freeInput.convertInput();
            methodOutEq.addAll(conversionResult.getSecond());
            conversionLocalList.addAll(conversionResult.getFirst());
        }
    }

    //entered by hand for now
    private void discoverStateInputPad() {
        stateInput.add("start_btn", NamedType.BOOL);
        stateInput.add("launch_btn", NamedType.BOOL);
        stateInput.add("reset_btn", NamedType.BOOL);
        stateInput.add("ignition", NamedType.BOOL);

        if (stateInput.containsBool()) { //type conversion to spf int type is needed
            Pair<ArrayList<VarDecl>, ArrayList<Equation>> conversionResult = stateInput.convertInput();
            typeConversionEq.addAll(conversionResult.getSecond());
            conversionLocalList.addAll(conversionResult.getFirst());
        }
    }

    //entered by hand for now - order is important, needs to match in order of the input
    private void discoverStateOutputPad() {
        stateOutput.add(referenceObjectName + ".start_btn.1.15.4", NamedType.BOOL);
        stateOutput.add(referenceObjectName + ".launch_btn.1.17.4", NamedType.BOOL);
        stateOutput.add(referenceObjectName + ".reset_btn.1.9.4", NamedType.BOOL);

        if (stateOutput.containsBool()) {
            ArrayList<Equation> conversionResult = stateOutput.convertOutput();
            typeConversionEq.addAll(conversionResult);
            //conversionLocalList.addAll(conversionResult.getFirst()); // no need to add this, since these are already as
            // def in the dynStmt
        }
    }


    //entered by hand for now

    private void discoverMethodOutputEven() {
        //methodOutput.add(referenceObjectName + ".countState.1.3.2", NamedType.INT);
        methodOutput.add(referenceObjectName + ".output.1.5.2", NamedType.INT);
        //  Pair<ArrayList<VarDecl>, ArrayList<Equation>> conversionResult = methodOutput.convertOutput();
        //  typeConversionEq.addAll(conversionResult.getSecond());
        //conversionLocalList.addAll(conversionResult.getFirst()); // no need to add this, since these are already as
        // def in the dynStmt
    }

    //entered by hand for now
    private void discoverFreeInputEven() {
        freeInput.add("signal", NamedType.BOOL);
        if (freeInput.containsBool()) {
            Pair<ArrayList<VarDecl>, ArrayList<Equation>> conversionResult = freeInput.convertInput();
            typeConversionEq.addAll(conversionResult.getSecond());
            conversionLocalList.addAll(conversionResult.getFirst());
        }
    }

    //entered by hand for now
    private void discoverStateInputEven() {
        stateInput.add("countState", NamedType.INT);
    }

    //entered by hand for now - order is important, needs to match in order of the input
    private void discoverStateOutputEven() {
        //       stateOutput.add("r351.countState.1.3.2", NamedType.INT);

    }


    public ArrayList<VarDecl> generateInputDecl() {
        ArrayList<VarDecl> inputDeclList = generateFreeInputDecl();
        inputDeclList.addAll(generateStateInputDecl());
        return inputDeclList;
    }

    public ArrayList<VarDecl> generateFreeInputDecl() {
        return generateLustreDecl(freeInput);
    }

    public ArrayList<VarDecl> generateStateInputDecl() {
        return generateLustreDecl(stateInput);
    }

    private ArrayList<VarDecl> generateLustreDecl(SpecInputOutput inputOutput) {
        return inputOutput.generateVarDecl();
    }

    public ArrayList<VarDecl> generaterMethodOutDeclList() {
        return methodOutput.generateVarDecl();
    }

    public ArrayList<VarDecl> generateOutputDecl() {
        return stateOutput.generateVarDecl();
    }

    /**
     * searches in all in input and output arrays to check if it is one in them
     *
     * @param s
     * @return
     */
    public boolean isInOutVar(String s, NamedType type) {
        return isFreeInVar(s, type) || isStateInVar(s, type) || isStateOutVar(s, type) || isMethodOutVar(s, type);
    }


    public boolean isFreeInVar(String varName, NamedType type) {
        return freeInput.contains(varName, type);
    }

    public boolean isStateInVar(String varName, NamedType type) {
        return stateInput.contains(varName, type);
    }

    public boolean isStateOutVar(String varName, NamedType type) {
        return stateOutput.contains(varName, type);
    }

    public boolean isMethodOutVar(String varName, NamedType type) {
        return methodOutput.contains(varName, type);
    }

    public boolean isMethodReturnVar(String name){
        return methodOutput.hasName(name);
    }


    public Pair<VarDecl, Equation> replicateMethodOutput(String outVarName) {
        return methodOutput.replicateMe(outVarName);
    }

    public NamedType getMethodOutType() {
        if (methodOutput.varList.size() == 0) {
            System.out.println("Method has no output, this is unexpected method signature for R! Aborting!");
            assert false;
        }
        return methodOutput.varList.get(0).getSecond();
    }

    public Collection<? extends Equation> getMethoudOutEq() {
        return methodOutEq;
    }

    public Expr getMethodReturnInit() {
        return methodOutput.getReturnInitVal();
    }
}
