package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ARepair.synthesis;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Contract;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DiscoverContract;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ARepair.CounterExampleQuery;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil;
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
import jkind.results.Signal;

import java.util.*;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config.*;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DiscoverContract.loopCount;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.MinimalRepair.MinimalRepairCheck.internalId;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.MinimalRepair.MinimalRepairDriver.candidateLoopCount;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.MinimalRepair.MinimalRepairDriver.knownRepairLoopCount;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil.findEqWithLhs;

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

    public Equation propertyEq;
    private int testCaseCounter = 0;

    //this is LinkedHashMap in the form of varName -> pair of location and type
    private static LinkedHashMap<String, MainTCVar> testCaseInputNameLoc = new LinkedHashMap<>();

    //private static LinkedHashMap<String, Pair<String, NamedType>> testCaseOutputNameLoc = new LinkedHashMap<>();

    public final Contract contract;

    private static String testCaseVarName = "ok";

    private static List<Expr> holeExprs;
    public static int maxK;


    public static void resetState() {
        maxK = 0;
    }

    public TestCaseManager(Contract contract, ArrayList<Hole> holes, JKindResult counterExResult) {
        this.contract = contract;
        testCaseInputNameLoc = createNamesofTestInputs();
        if (!(holes.get(0) instanceof Expr)) {
            System.out.print("holes here must be their expression version. Aborting");
            assert false;
        }

        holeExprs = (ArrayList<Expr>) (ArrayList<?>) (holes);
        collectCounterExample(counterExResult);
    }


    public void collectCounterExample(JKindResult counterExResult) {

        for (PropertyResult pr : counterExResult.getPropertyResults()) {
            if (pr.getProperty() instanceof InvalidProperty) {
                InvalidProperty ip = (InvalidProperty) pr.getProperty();
                Counterexample counterExample = ip.getCounterexample();
                String fileName;
                if (Config.specLevelRepair)
                    fileName = currFaultySpec + "_" + loopCount + "_" + "CEX.lus";
                else
                    fileName = "def_" + currFaultySpec + "_" + DiscoverContract.permutationCount + "_" + loopCount + "_" + "CEX" +
                            ".lus";

                DiscoveryUtil.writeToFile(fileName, counterExample.toString(), false);
                translateTestCase(counterExample);
            }
        }
    }


    public void collectCounterExampleMinimal(JKindResult counterExResult, Node lastSynMainNode) {

        for (PropertyResult pr : counterExResult.getPropertyResults()) {
            if (pr.getProperty().getName().equals(Config.candidateSpecPropertyName)) {
                assert pr.getProperty() instanceof InvalidProperty;

                InvalidProperty ip = (InvalidProperty) pr.getProperty();
                Counterexample counterExample = ip.getCounterexample();
                String fileName;

                fileName = currFaultySpec + "_" + knownRepairLoopCount + "_" + candidateLoopCount + "_" +
                        "existsCEX.lus";
                DiscoveryUtil.writeToFile(fileName, counterExample.toString(), true);
                translateTestCaseMinimal(counterExample, lastSynMainNode);
                return;
            }
        }
    }


    public void translateTestCase(Counterexample counterExResult) {
        testCaseCounter++;

        List<VarDecl> localTestInputVars = createVarDeclForTestInput(true); //assuming that the tightness is okay,
        // that is we are not in the case of creating a tightness test case, where the itTighter property is false.
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


    public void translateTestCaseMinimal(Counterexample counterExResult, Node lastSynMainNode) {

        Signal<BooleanValue> isMatchImpl = findCEXvarOut(counterExResult, "isMatchImpl");
        Signal<BooleanValue> isTighter = findCEXvarOut(counterExResult, "isTighter");
        testCaseCounter++;
        boolean isTighterCEX = isTighter.getValue(counterExResult.getLength() - 1).value;

        List<VarDecl> localTestInputVars = createVarDeclForTestInput(isTighterCEX);
        VarDecl localTestCallVar = createTestCallVars();

        List<Equation> localTestInputEqs = makeTestInputEqsMinimal(counterExResult, localTestInputVars, isTighterCEX);

        Equation localTestCallEq = makeTestCallEq(counterExResult, localTestInputVars, localTestCallVar);

        Equation localPropertyEq = makeMinimalPropertyEq(isMatchImpl.getValue(counterExResult.getLength() - 1), isTighter.getValue(counterExResult.getLength() - 1), localTestCallVar, lastSynMainNode);

        testInputVars.addAll(localTestInputVars);
        testCallVars.add(localTestCallVar);
        testInputEqs.addAll(localTestInputEqs);
        testCallEqs.add(localTestCallEq);

        propertyEq = localPropertyEq;
    }

    private Equation makeMinimalPropertyEq(BooleanValue isMatchImpl, BooleanValue isTighter, VarDecl localTestCallVar, Node lastSynMainNode) {
        Equation oldFailEq = findEqWithLhs(lastSynMainNode.equations, "fail");

        Equation newFailEq;

        assert oldFailEq.expr instanceof UnaryExpr;

        Expr oldInnerExpr = ((UnaryExpr) oldFailEq.expr).expr;

        Expr newInnerExpr = null;

        if ((!isMatchImpl.value) && (isTighter.value))//then add the new test case in affirmative form
            newInnerExpr = new BinaryExpr(DiscoveryUtil.varDeclToIdExpr(localTestCallVar), BinaryOp.AND, oldInnerExpr);
        else if ((isMatchImpl.value) && (!isTighter.value))//then we need to add in the neg form, assuming that the
            // test case collected so far captures the behaviour of upper property that we are trying to find a
            // tighter version of. The only way that we can come here the candidate property was true but the upper
            // property was false, in this case we want to ensure that on that test input we want to see a false
            // behaviour just like the upper property.
            newInnerExpr = new BinaryExpr(new UnaryExpr(UnaryOp.NOT, DiscoveryUtil.varDeclToIdExpr(localTestCallVar)), BinaryOp.AND, oldInnerExpr);
            //newInnerExpr = new BinaryExpr(DiscoveryUtil.varDeclToIdExpr(localTestCallVar), BinaryOp.AND, oldInnerExpr);
        else if ((!isMatchImpl.value) && (!isTighter.value)) {
            //this case were both are false is interesting and is in tight behaviour with the test case being
            // collected, that is if we collected the test case of being matching the implementation then we need to
            // add the test case in an affirmative form, however if we collected the test case of the upper property
            // then we need to add the test case in the neg form.
            //According to createVarDeclForTestInput , we collect in this case the test case of the upper property thus
            // we will
            // construct
            // the
            // neg form of the test case.
            newInnerExpr = new BinaryExpr(new UnaryExpr(UnaryOp.NOT, DiscoveryUtil.varDeclToIdExpr(localTestCallVar)), BinaryOp.AND, oldInnerExpr);
        } else {
            System.out.print("this can't happen, both isMatchImpl and isTighter are true yet we are collecting the counter example!");
            assert false;
        }

        newFailEq = new Equation(oldFailEq.lhs, new UnaryExpr(UnaryOp.NOT, newInnerExpr));
        return newFailEq;
    }


    private Signal<BooleanValue> findCEXvarOut(Counterexample counterExResult, String isMatchImpl) {
        return counterExResult.getBooleanSignal(isMatchImpl);
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

        for (Map.Entry<String, MainTCVar> entry : testCaseInputNameLoc.entrySet()) {
            if (entry.getValue().purpose != Purpose.TIGHTEROUTPUT) {
                String varName = entry.getKey();
                String location = entry.getValue().location;
                NamedType varType = entry.getValue().type;

                String smtVarName = String.valueOf(createSmtVarName(varName, location, entry.getValue().purpose));

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
        }
        checkAndAddTestCase(new TestCase(testCaseMap));

        return testInputEqs;
    }

    private List<Equation> makeTestInputEqsMinimal(Counterexample counterExResult, List<VarDecl> localTestInputVars, boolean isTighter) {
        List<Equation> testInputEqs = new ArrayList<>();

        int varDeclIndex = 0;
        HashMap<String, List<Value>> testCaseMap = new HashMap<>();

        for (Map.Entry<String, MainTCVar> entry : testCaseInputNameLoc.entrySet()) {

            String varName = entry.getKey();
            String location = entry.getValue().location;
            NamedType varType = entry.getValue().type;
            Purpose purpose = entry.getValue().purpose;

            if ((isTighter && purpose != Purpose.TIGHTEROUTPUT) || (!isTighter && purpose != Purpose.IMPLEMENTATIONOUTPUT)) {

                String smtVarName = String.valueOf(createSmtVarName(varName, location, purpose));

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

    //creates the nammes expected to appear in the counter example, if the names of the var are in main or exists in other node, then they will have different prefix. similarly, if the purpose of the var is to capture the tightness output, then we need to append its "internalId" that distinguish the output of these tpes of variables.
    private String createSmtVarName(String varName, String location, Purpose purpose) {
        if (location.equals("main") && (purpose != Purpose.TIGHTEROUTPUT))
            return varName;
        else if (location.equals("main") && (purpose == Purpose.TIGHTEROUTPUT))
            return varName + internalId;
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
     * isTighter: indicates if the tightness property is not holding or not. For the outer loop of non-minimal we
     * assume that the isTight holds.
     * <p>
     * Assumption here about the created test input if the counter example had both isTighter and matchImp both being
     * false, in this case the test case is created with the input of the upper property, and therefore, it is in
     * tight connection with how the equation of fail is being created, in this case it should appear in the neg form.
     *
     * @return
     */
    private List<VarDecl> createVarDeclForTestInput(boolean isTighter) {
        List<VarDecl> testCaseInputVars = new ArrayList<>();

        for (Map.Entry<String, MainTCVar> entry : testCaseInputNameLoc.entrySet()) {
            Purpose purpose = entry.getValue().purpose;


            if ((isTighter && purpose != Purpose.TIGHTEROUTPUT) || (!isTighter && purpose != Purpose.IMPLEMENTATIONOUTPUT)) {
                String testCaseVarName = entry.getKey() + (testCaseCounter - 1);
                testCaseInputVars.add(new VarDecl(testCaseVarName, entry.getValue().type));
            }
        }
        return testCaseInputVars;
    }


    /**
     * Collects the names of vars and their location and type. These are the names of the variables we would like to look up their valuation to prepare testcases.
     *
     * @return
     */
    private LinkedHashMap<String, MainTCVar> createNamesofTestInputs() {

        //test cases needs to have the inputs of the main (not the input in the main that are actually output) and the output of the r_wrapper

        SpecInputOutput mainFreeInput = this.contract.tInOutManager.getFreeInputs();

        //contains all the vars to be passed in the call except the hole vars, and it attaches with every one of those its location.
        LinkedHashMap<String, MainTCVar> testCaseInputVars = collectTestCaseInputs(mainFreeInput, "main");

        //this collects the specific output variable we would like to see if we are looking for tighter testcase. This is because at the time of checking the forall part of the minimality
        //we can have two test cases, on if we are not matching the implementation and other if it is not tighter, in every test case the output we need to be collected is different.
        testCaseInputVars.putAll(getContractOutput());

        //the output is exactly the output of the wrapper which has the same type as the method output of the R node
        //testCaseInputVars.put("out", new Pair(WRAPPERNODE, this.contract.rInOutManager.getMethodOutType()));
        testCaseInputVars.putAll(getWrapperOutput());


        //      testCaseInputVars.putAll(testCaseInputOutVars);

        return testCaseInputVars;
    }

    private Map<? extends String, MainTCVar> getWrapperOutput() {
        LinkedHashMap<String, MainTCVar> wrapperOutputTCvars = new LinkedHashMap<>();

        for (VarDecl out : CounterExampleQuery.rWrapper.outputs) {
            assert (out.type instanceof NamedType);
            wrapperOutputTCvars.put(out.id, new MainTCVar(out.id, WRAPPERNODE, (NamedType) out.type, Purpose.IMPLEMENTATIONOUTPUT));
        }
        return wrapperOutputTCvars;
    }


    private Map<? extends String, MainTCVar> getContractOutput() {
        LinkedHashMap<String, MainTCVar> wrapperOutputTCvars = new LinkedHashMap<>();

        for (Pair<String, NamedType> varDecl : contract.tInOutManager.getInOutput().varList) {
            wrapperOutputTCvars.put(varDecl.getFirst(), new MainTCVar(varDecl.getFirst(), "main", varDecl.getSecond(), Purpose.TIGHTEROUTPUT));
        }
        return wrapperOutputTCvars;
    }

    /**
     * this composes the test case inputs as a linkedhashmap of the form testInputStrName -> Pair(location, NamedType)
     *
     * @param mainFreeInput
     * @param location
     * @return
     */
    private LinkedHashMap<String, MainTCVar> collectTestCaseInputs(SpecInputOutput mainFreeInput, String location) {
        LinkedHashMap<String, MainTCVar> inputList = new LinkedHashMap<>();

        for (int i = 0; i < mainFreeInput.getSize(); i++) {
            Pair<String, NamedType> varNameType = mainFreeInput.varList.get(i);
            inputList.put(varNameType.getFirst(), new MainTCVar(varNameType.getFirst(), location, varNameType.getSecond(), Purpose.INPUT));
        }
        return inputList;
    }

    public static String createTestVarStr(int prefix) {
        return (testCaseVarName + "_" + prefix);
    }

}
