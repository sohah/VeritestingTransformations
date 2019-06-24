package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.synthesis;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Contract;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DiscoverContract;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.SpecInputOutput;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import jkind.api.results.JKindResult;
import jkind.api.results.PropertyResult;
import jkind.lustre.*;
import jkind.lustre.values.BooleanValue;
import jkind.lustre.values.IntegerValue;
import jkind.lustre.values.Value;
import jkind.results.Counterexample;
import jkind.results.InvalidProperty;

import java.util.*;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config.*;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DiscoverContract.contractMethodName;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.synthesis.SynthesisContract.getHoleExpr;

/**
 * This is used to increment the test cases equations and locals.
 */
public class TestCaseManager {

    public final List<VarDecl> testInputVars = new ArrayList<>();
    public final List<VarDecl> testCallVars = new ArrayList<>();

    public final List<Equation> testInputEqs = new ArrayList<>();
    public final List<Equation> testCallEqs = new ArrayList<>();

    //maintains all test cases generated to check that it cant' be repeated
    public List<TestCase> testCases = new ArrayList<>();

    Equation propertyEq;
    private static int testCaseCounter = 0;

    //this is LinkedHashMap in the form of varName -> pair of location and type
    private static LinkedHashMap<String, Pair<String, NamedType>> testCaseInputNameLoc = new LinkedHashMap<>();

    //private static LinkedHashMap<String, Pair<String, NamedType>> testCaseOutputNameLoc = new LinkedHashMap<>();

    public final Contract contract;

    private static String testCaseVarName = "ok";

    private static List<Expr> holeExprs;
    public static int maxK;


    public TestCaseManager(Contract contract, JKindResult counterExResult) {
        this.contract = contract;
        testCaseInputNameLoc = createNamesofTestInputs();
        holeExprs = getHoleExpr();
        collectCounterExample(counterExResult);
    }


    public void collectCounterExample(JKindResult counterExResult) {

        for (PropertyResult pr : counterExResult.getPropertyResults()) {
            if (pr.getProperty() instanceof InvalidProperty) {
                InvalidProperty ip = (InvalidProperty) pr.getProperty();
                Counterexample counterExample = ip.getCounterexample();
                String fileName = contractMethodName + loopCount + "CEX.lus";

                DiscoveryUtil.writeToFile(fileName, counterExample.toString());
                translateTestCase(counterExample);
            }
        }
    }


    public void translateTestCase(Counterexample counterExResult) {
        testCaseCounter++;

        List<VarDecl> localTestInputVars = createVarDeclForTestInput();
        VarDecl localTestCallVar = createTestCallVars();

        List<Equation> localTestInputEqs = makeTestInputEqs(counterExResult, localTestInputVars);

        Equation localTestCallEq = makeTestCallEq(counterExResult, localTestInputVars, localTestCallVar);

        Equation localPropertyEq = makePropertyEq();

        testInputVars.addAll(localTestInputVars);
        testCallVars.add(localTestCallVar);
        testInputEqs.addAll(localTestInputEqs);
        testCallEqs.add(localTestCallEq);

        propertyEq = localPropertyEq;
    }

    /**
     * This is used to collect the values of a single input over a stream of inputs that defines different valuations of the input in different k step. Here we use the testCaseNameLoc and testCaseOutputNameLoc, to create the right form of fields in smt form using the location name. This creates the pre and followed by expression of the input.
     *
     * @param counterExResult
     * @param localTestInputVars
     * @return
     */
    private List<Equation> makeTestInputEqs(Counterexample counterExResult, List<VarDecl> localTestInputVars) {
        List<Equation> testInputEqs = new ArrayList<>();

        int varDeclIndex = 0;
        HashMap<String, List<Value>> testCaseMap = new HashMap<>();

        for (Map.Entry<String, Pair<String, NamedType>> entry : testCaseInputNameLoc.entrySet()) {
            String varName = entry.getKey();
            String location = entry.getValue().getFirst();
            NamedType varType = entry.getValue().getSecond();

            String smtVarName = String.valueOf(createSmtVarName(varName, location));

            List<Value> values = getVarTestValues(counterExResult, smtVarName, varType);

            testCaseMap.put(varName, values);

            IdExpr lhs = DiscoveryUtil.varDeclToIdExpr(localTestInputVars.get(varDeclIndex));

            Expr rhs = createValueExpr(varType, values.get(values.size() - 1));

            for (int i = values.size() - 2; i >= 0; i--) {
                rhs = new UnaryExpr(UnaryOp.PRE, rhs);
                rhs = new BinaryExpr(createValueExpr(varType, values.get(i)), BinaryOp.ARROW, rhs);
            }

            testInputEqs.add(new Equation(lhs, rhs));
            varDeclIndex++;
        }

        checkAndAddTestCase(new TestCase(testCaseMap));

        return testInputEqs;
    }

    /**
     * checks if we are encountering a repeated test case.
     *
     * @param testCase
     */
    private void checkAndAddTestCase(TestCase testCase) {
        Iterator<TestCase> testCasesItr = testCases.iterator();
        while (testCasesItr.hasNext()) {
            TestCase tc = testCasesItr.next();
            if (testCase.isEqual(tc)) {
                System.out.println("repeated test case! printing and aborting");
                //System.out.println("new test case:" + testCase.toString());
                //System.out.println("old test case" + tc.toString());

                assert false;
            }
        }
        testCases.add(testCase);
    }

    private Expr createValueExpr(NamedType varType, Value value) {
        if (varType == NamedType.BOOL)
            return new BoolExpr(((BooleanValue) value).value);
        else if (varType == NamedType.INT)
            return new IntExpr(((IntegerValue) value).value);
        else {
            System.out.println("unsupported type");
            assert false;
            return null;
        }
    }

    private List<Value> getVarTestValues(Counterexample counterExResult, String smtVarName, NamedType varType) {
        int maxK = counterExResult.getLength();

        List<Value> values = new ArrayList<>();

        for (int i = 0; i < maxK; i++) {
            if (varType == NamedType.BOOL) {
                values.add(counterExResult.getBooleanSignal(smtVarName).getValue(i));
            } else if (varType == NamedType.INT) {
                values.add(counterExResult.getIntegerSignal(smtVarName).getValue(i));
            } else
                assert false; //unsupported type.
        }
        return values;
    }


    private String createSmtVarName(String varName, String location) {
        if (location.equals("main"))
            return varName;
        else {
            assert (location.equals(WRAPPERNODE));
            return WRAPPERNODE + "~0." + varName;
        }

    }

    private Equation makePropertyEq() {

        assert (testCaseCounter > 0);

        IdExpr lhs = new IdExpr(counterExPropertyName);
        Expr rhs;

        if (testCaseCounter == 1)
            rhs = new IdExpr(createTestVarStr(0));
        else
            rhs = new BinaryExpr(new IdExpr(createTestVarStr(0)), BinaryOp.AND, new IdExpr(createTestVarStr(1)));

        for (int i = 2; i < testCaseCounter; i++) {
            rhs = new BinaryExpr(rhs, BinaryOp.AND, new IdExpr(createTestVarStr(i)));
        }

        return new Equation(lhs, new UnaryExpr(UnaryOp.NOT, rhs));
    }

    private void updateMaxK(int newK) {
        maxK = (newK > maxK) ? newK : maxK;
    }

    public int getMaxK() {
        return maxK;
    }

    private Equation makeTestCallEq(Counterexample counterExResult, List<VarDecl> testInputVars, VarDecl testCallVar) {

        IdExpr lhs = DiscoveryUtil.varDeclToIdExpr(testCallVar);

        List<Expr> rhsParameters = (ArrayList<Expr>) (ArrayList<?>) DiscoveryUtil.varDeclToIdExpr(testInputVars);

        rhsParameters.addAll(holeExprs);

        int k = counterExResult.getLength();
        rhsParameters.add(new IntExpr(k - 1));

        updateMaxK(k);

        NodeCallExpr rhs = new NodeCallExpr(CHECKSPECNODE, rhsParameters);

        Equation testCaseEq = new Equation(lhs, rhs);

        return testCaseEq;

    }

    private VarDecl createTestCallVars() {
        VarDecl testCaseVar = new VarDecl(createTestVarStr(testCaseCounter - 1), NamedType.BOOL);
        return testCaseVar;
    }

    /**
     * uses the populated testCaseInputLoc to generate a VarDecl list for all the enteries.
     *
     * @return
     */
    private List<VarDecl> createVarDeclForTestInput() {
        List<VarDecl> testCaseInputVars = new ArrayList<>();

        for (Map.Entry<String, Pair<String, NamedType>> entry : testCaseInputNameLoc.entrySet()) {
            String testCaseVarName = entry.getKey() + (testCaseCounter - 1);
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

        testCaseInputVars.put("out", new Pair(WRAPPERNODE, NamedType.BOOL));
        return testCaseInputVars;
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
