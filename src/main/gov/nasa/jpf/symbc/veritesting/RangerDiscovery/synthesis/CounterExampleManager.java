package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.synthesis;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Contract;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DiscoverContract;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.SpecInputOutput;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import ia_parser.Exp;
import jkind.api.results.JKindResult;
import jkind.api.results.PropertyResult;
import jkind.lustre.*;
import jkind.results.Counterexample;
import jkind.results.InvalidProperty;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.synthesis.SynthesisContract.getHoleExpr;

/**
 * This is used to increment the test cases equations and locals.
 */
public class CounterExampleManager {

    public final List<VarDecl> testInputVars = new ArrayList<>();
    public final List<VarDecl> testCallVars = new ArrayList<>();

    public final List<Equation> testInputEqs = new ArrayList<>();
    public final List<Equation> testCallEqs = new ArrayList<>();

    Equation propertyEq;
    private static int testCaseCounter = 0;

    //this is LinkedHashMap in the form of varName -> pair of location and type
    private static LinkedHashMap<String, Pair<String, NamedType>> testCaseInputNameLoc = new LinkedHashMap<>();

    private static LinkedHashMap<String, Pair<String, NamedType>> testCaseOutputNameLoc = new LinkedHashMap<>();

    public final Contract contract;

    private static String testCaseVarName = "ok";


    public CounterExampleManager(Contract contract) {
        this.contract = contract;
        testCaseInputNameLoc = createNamesofTestInputs();
        testCaseOutputNameLoc = createNamesofTestOutputs();
    }


    public void collectCounterExample(JKindResult counterExResult) {

        for (PropertyResult pr : counterExResult.getPropertyResults()) {
            if (pr.getProperty() instanceof InvalidProperty) {
                InvalidProperty ip = (InvalidProperty) pr.getProperty();
                Counterexample counterExample = ip.getCounterexample();
                translateTestCase(counterExample);
            }
        }
    }


    public void translateTestCase(Counterexample counterExResult) {
        List<VarDecl> localTestInputVars = createVarDeclForTestInput();
        VarDecl localTestCallVars = createVarDeclForOkOutput();

        Equation localTestCallEq = makeTestCaseEq(testInputVars, localTestCallVars);
        List<Equation> localTestInputEqs = makeTestInputEqs();

        Equation localPropertyEq = makePropertyEq();

        testInputVars.addAll(localTestInputVars);
        testCallVars.add(localTestCallVars);
        testInputEqs.addAll(localTestInputEqs);
        testCallEqs.add(localTestCallEq);

        propertyEq = localPropertyEq;
    }

    private Equation makePropertyEq() {

        assert (testCaseCounter > 0);

        IdExpr lhs = new IdExpr(testCaseVarName);
        Expr rhs;

        if (testCaseCounter == 1)
            rhs = new IdExpr(createTestVarStr(0));
        else
            rhs = new BinaryExpr(new IdExpr(createTestVarStr(0)), BinaryOp.AND, new IdExpr(createTestVarStr(1)));

        for (int i = 2; i <= testCaseCounter; i++) {
            rhs = new BinaryExpr(rhs, BinaryOp.AND, new IdExpr(createTestVarStr(i)));
        }

        return new Equation(lhs, rhs);
    }


    private static Equation makeTestCaseEq(List<VarDecl> testInputVars, VarDecl testCaseOkVars) {

        IdExpr lhs = DiscoveryUtil.varDeclToIdExpr(testCaseOkVars);

        List<Expr> rhsParameters = (ArrayList<Expr>) (ArrayList<?>) DiscoveryUtil.varDeclToIdExpr(testInputVars);

        rhsParameters.addAll(getHoleExpr());

        NodeCallExpr rhs = new NodeCallExpr(DiscoverContract.CHECKSPECNODE, rhsParameters);

        Equation testCaseEq = new Equation(lhs, rhs);

        return testCaseEq;

    }

    private VarDecl createVarDeclForOkOutput() {
        VarDecl testCaseVar = new VarDecl(createTestVarStr(testCaseCounter), NamedType.BOOL);
        return testCaseVar;
    }

    /**
     * usese the populated testCaseInputLoc to generate a VarDecl list for all the enteries.
     *
     * @return
     */
    private List<VarDecl> createVarDeclForTestInput() {
        List<VarDecl> testCaseInputVars = new ArrayList<>();

        for (Map.Entry<String, Pair<String, NamedType>> entry : testCaseInputNameLoc.entrySet()) {
            String testCaseVarName = entry.getKey() + testCaseCounter;
            testCaseInputVars.add(new VarDecl(testCaseVarName, entry.getValue().getSecond()));
        }
        return testCaseInputVars;
    }


    /**
     * this creates a pair of the Name and the Location of the test input. The location will later be used to compose the SMT name for the input to search in the counter example.
     *
     * @return
     */
    private LinkedHashMap<String, Pair<String, NamedType>> createNamesofTestInputs() {

        //test cases needs to have the inputs of the main (not the input in the main that are actually output) and the output of the r_wrapper

        SpecInputOutput mainFreeInput = this.contract.tInOutManager.getFreeInputs();

        //contains all the vars to be passed in the call except the hole vars, and it attaches with every one of those its location.
        LinkedHashMap<String, Pair<String, NamedType>> testCaseInputVars = collectTestCaseInputs(mainFreeInput, "main");

        return testCaseInputVars;
    }


    private LinkedHashMap<String, Pair<String, NamedType>> createNamesofTestOutputs() {

        LinkedHashMap<String, Pair<String, NamedType>> testCaseOutVars = new LinkedHashMap<>();

        testCaseOutVars.put("out", new Pair("out", DiscoverContract.WRAPPERNODE));
        return testCaseOutVars;
    }


    /**
     * this composes the test case inputs as a linkedhashmap of the form testInputStrName -> Pair(location, NamedType)
     *
     * @param mainFreeInput
     * @param location
     * @return
     */
    private LinkedHashMap<String, Pair<String, NamedType>> collectTestCaseInputs(SpecInputOutput mainFreeInput, String location) {
        LinkedHashMap<String, Pair<String, NamedType>> inputList = new LinkedHashMap<>();

        for (int i = 0; i < mainFreeInput.getSize(); i++) {
            Pair<String, NamedType> varNameType = mainFreeInput.varList.get(i);
            inputList.put(varNameType.getFirst(), new Pair(location, varNameType.getSecond()));
        }
        return inputList;
    }

    private String createTestVarStr(int prefix) {
        return (testCaseVarName + "_" + prefix);
    }


}
