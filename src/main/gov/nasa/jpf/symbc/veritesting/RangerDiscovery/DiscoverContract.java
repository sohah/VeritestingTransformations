package gov.nasa.jpf.symbc.veritesting.RangerDiscovery;

import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.vm.*;
import za.ac.sun.cs.green.expr.Expression;

import java.util.*;

public class DiscoverContract {

    public static String contractMethodName;

    public static boolean active = true;
    public static boolean rangerMode;
    // a unique post fix for ranger variables to destinguish them from jkind variables
    public static String rangerPostFix ="$r";


    enum InputOutput {INPUT, OUTPUT}

    private static ArrayList<String> rFreeInput = new ArrayList<>();
    private static ArrayList<String> rStateInput = new ArrayList<>();
    private static ArrayList<String> rStateOutput = new ArrayList<>();
    private static ArrayList<String> rIntermediateVar = new ArrayList<>();

    private static ArrayList<String> jkindInVar = new ArrayList<>();
    private static ArrayList<String> jkindOutVar = new ArrayList<>();


    /**
     * Ranger Contract helper functions by making DiscoverContract class as an mediator
     *****************/
    public static void setRangerRegion(DynamicRegion dynRegion) {
        RangerContract.dynRegion = dynRegion;
    }

    public static void collectRinput(ThreadInfo ti, Expression[] params, String currClassName, DynamicRegion dynRegion) {
        RangerContract.collectInput(ti, params, currClassName, dynRegion);
    }

    public static <T> ArrayList<Pair> getZ3QuerySet() {
        return RangerContract.z3QuerySet;
    }

    /**
     * Ranger Contract helper functions by making DiscoverContract class as an mediator
     *****************/


    public static String generateKMerge(String query, ArrayList z3FunDecSet, String fileName) {

        JkindContract.discoverJKindVars();
        RangerContract.discoverRangerVars();

        rFreeInput = RangerContract.freeInput;
        rStateInput = RangerContract.stateInput;
        rStateOutput = RangerContract.stateOutput;
        rIntermediateVar = RangerContract.intermediateVar;

        jkindInVar = JkindContract.jkindInVar;
        jkindOutVar = JkindContract.jkindOutVar;


        String jkindTransition = JkindContract.getJkindTransition();

        String rangerTransition = generateRangerTransition(query, z3FunDecSet, fileName);

        rangerTransition += generateContractAssertion();

        return (jkindTransition + rangerTransition + "\n(get-model)");

    }


    /**
     * used to generate a transition function R for discovery of the contract of the implementation.
     *
     * @param query
     * @param z3FunDecSet
     * @param fileName
     * @return
     */
    public static String generateRangerTransition(String query, ArrayList z3FunDecSet, String fileName) {
        rIntermediateVar = z3FunDecSet;

        RangerContract.dumpInputOutput(fileName);
        String transitionHeader = generateTransitionHeader();
        String body = generateBody(query);
        body = "(and \n \t(= symVar 1)\n" + body + ")";

        String rangerTransition = transitionHeader + body + ")";

        String instantiation0 = generateInstanitaion(0) + "\n";
        String instantiation1 = generateInstanitaion(1) + "\n";

        return rangerTransition + "\n" + instantiation0 + "\n" + instantiation1;
    }


    private static String generateInstanitaion(int i) {
        //instance variable declarations
        String varInstance_i = declareVarInstance(i);

        //r binding to the declarations above.
        String rInstance = declareRInstance(i);
        return varInstance_i + "\n" + rInstance;
    }

    private static String declareRInstance(int i) {
        String R = "(assert (R ";
        String varBinds = "";
        varBinds += generateBinds(rFreeInput, i);
        if (i == 0)
            varBinds += generateBinds(rStateInput, i);
        else
            varBinds += generateBinds(rStateOutput, i - 1);

        varBinds += generateBinds(rStateOutput, i);
        varBinds += generateBinds(rIntermediateVar, i);

        return R + varBinds + " ))";
    }

    private static String generateBinds(ArrayList<String> arrayList, int i) {
        String bind = "";

        for (String varName : arrayList) {
            bind += " " + generateVarName(varName, i);
        }

        return bind;
    }

    private static String declareVarInstance(int i) {
        String declareInState_i = "";
        String declareFree_i;
        String declareOutput_i;
        String intermediateVar_i;
        if (i == 0)
            declareInState_i = declareVars_i(0, rStateInput);

        declareFree_i = declareVars_i(i, rFreeInput);
        declareOutput_i = declareVars_i(i, rStateOutput);
        intermediateVar_i = declareVars_i(i, rIntermediateVar);

        return declareFree_i + declareInState_i + declareOutput_i + intermediateVar_i;

    }

    private static String declareVars_i(int i, ArrayList<String> stateInput) {
        String inState = "";
        for (String varName : stateInput) {
            inState += "(declare-fun " + generateVarName(varName, i) + " () Int)\n";
        }
        return inState;
    }

    private static String generateVarName(String varName, int i) {
        return varName + rangerPostFix + i;
    }


    private static String generateTransitionHeader() {
        String header = "(define-fun R (";
        String parameters = "";
        rIntermediateVar.removeAll(rStateInput);
        rIntermediateVar.removeAll(rStateOutput);
        rIntermediateVar.removeAll(rFreeInput);

        parameters += createParameters(rFreeInput);
        parameters += createParameters(rStateInput);
        parameters += createParameters(rStateOutput);
        parameters += createParameters(rIntermediateVar);

        header += parameters + ") Bool\n";

        return header;
    }


    private static String createParameters(ArrayList<String> inputArray) {
        String parameters = "";
        for (String varName : inputArray) {
            parameters += "(" + varName + " Int) ";
        }
        return parameters;
    }


    private static String generateBody(String query) {
        assert (query.length() > 0);

        String constraints = new String();
        /*removing the outer solve*/
        query = query.substring(8, query.length() - 1);

        int startingIndex = 0;
        int endingIndex = query.length();
        while (startingIndex < endingIndex) {
            Pair startEndIndecies = findAssertion(query, startingIndex);

            startingIndex = (int) startEndIndecies.getFirst();
            int assertionEndIndex = (int) startEndIndecies.getSecond();

            String assertion = query.substring(startingIndex, assertionEndIndex + 1); //+1 because substring is not inclusive for the endIndex.
            constraints += "\t" + assertion + "\n";
            startingIndex = assertionEndIndex + 1;
        }
        return constraints;
    }


    public static String generateContractAssertion() {
        String trailId = "contract_match$";
        String mergePredicate = "; ---------- joining contract begins here -------------\n(declare-fun " + trailId + "() bool)\n";
        mergePredicate += "\n(assert(= " + trailId + "\n\t(let ";

        ArrayList<String> rK1Input = generateRforKVarNames(rFreeInput, 0);
        rK1Input.addAll(generateRforKVarNames(rStateInput, 0));
        ArrayList<String> rK1Output = generateRforKVarNames(rStateOutput, 0);

        ArrayList<String> rK2Input = generateRforKVarNames(rFreeInput, 1);
        rK2Input.addAll(generateRforKVarNames(rStateOutput, 0));
        ArrayList<String> rK2Output = generateRforKVarNames(rStateOutput, 1);

        String inputMatchPredicate_1 = generateMatchPredicate(InputOutput.INPUT, rK1Input, -1);
        String outputMatchPredicate_1 = generateMatchPredicate(InputOutput.OUTPUT, rK1Output, -1);

        String inputMatchPredicate_0 = generateMatchPredicate(InputOutput.INPUT, rK2Input, 0);
        String outputMatchPredicate_0 = generateNotMatchPredicate(InputOutput.OUTPUT, rK2Output, 0);

        mergePredicate += "(" + inputMatchPredicate_1 + outputMatchPredicate_1 + inputMatchPredicate_0 + outputMatchPredicate_0 + ")";
        mergePredicate += "\t\t( and input_match~1 output_match~1 input_match$1 (not output_match$1))\n";

        mergePredicate += ")))\n " +
                "(check-sat " + trailId + ") \n; ---------- joining contract ends here -------------\n";
        return mergePredicate;
    }

    private static ArrayList<String> generateRforKVarNames(ArrayList<String> rFreeInput, int i) {
        ArrayList<String> newList = new ArrayList<String>();

        String rPostFix = rangerPostFix + i;
        for (String var : rFreeInput) {
            newList.add(var + rPostFix);
        }
        return newList;
    }

    private static String generateNotMatchPredicate(InputOutput output, ArrayList rOutput, int k) {
        assert (output == InputOutput.OUTPUT);

        String notMatchPredicate = "\n\t(output_match$1" + "\n\t\t( and \n";
        int index = 0;
        for (String jkindVar : jkindOutVar) {
            notMatchPredicate += createNotClause(jkindVar, (String) rOutput.get(index), k);
            ++index;
        }

        notMatchPredicate += "))\n";

        return notMatchPredicate;

    }

    private static String createNotClause(String jkindVar, String rangerVar, int k) {
        String jKindPostFix = "";
        if (k == -1)
            jKindPostFix = "$0";
        else if (k == 0)
            jKindPostFix = "$1";

        if (JkindContract.jkindTypeTable.get(jkindVar) == null) //assuming it is a bool then
            return ("\t\t\t(= " + "$" + jkindVar + jKindPostFix + "(= " + rangerVar + " 1))\n");
        else
            return ("\t\t\t (= " + "$" + jkindVar + jKindPostFix + "  " + rangerVar + ")\n");
    }

    private static String generateMatchPredicate(InputOutput inputOutput, ArrayList rList, int k) {
        String matchPredicate = "";
        ArrayList<String> jInputOutputList;

        if (inputOutput == InputOutput.INPUT) {
            matchPredicate = (k == -1) ? "\t( input_match~1" : "( input_match$1";
            jInputOutputList = jkindInVar;
        } else {
            matchPredicate = (k == -1) ? "\t( output_match~1" : "( output_match$1";
            jInputOutputList = jkindOutVar;
        }
        matchPredicate += "\n\t(and\n";
        int index = 0;


        for (String jkindVar : jInputOutputList) {
            matchPredicate += createClause(inputOutput, jkindVar, (String) rList.get(index), k);
            ++index;
        }

        matchPredicate += "))\n";

        return matchPredicate;
    }

    private static boolean isRangerFreeInput(String s) {
        boolean exits = false;
        int index = 0;
        while (!exits && index <= rFreeInput.size()) {
            if (rFreeInput.contains(s))
                exits = true;
            ++index;
        }
        return exits;
    }

    private static String createClause(InputOutput inputOutput, String jkindVar, String rangerVar, int k) {
        String jKindPostFix = "";
        if ((inputOutput == InputOutput.INPUT) && (k == -1))
            jKindPostFix = "$~1";
        else if ((inputOutput == InputOutput.OUTPUT) && (k == -1))
            jKindPostFix = "$0";
        else if ((inputOutput == InputOutput.INPUT) && (k == 0))
            jKindPostFix = "$0";
        else if ((inputOutput == InputOutput.OUTPUT) && (k == 0))
            jKindPostFix = "$1";

        if (JkindContract.jkindTypeTable.get(jkindVar) == null) //assuming it is a bool then
            return ("\t\t\t(= " + "$" + jkindVar + jKindPostFix + " (= " + rangerVar + " 1 ))\n");
        else //assuming int
            return ("\t\t\t(= " + "$" + jkindVar + jKindPostFix + " " + rangerVar + ")\n");
    }


    /**
     * This takes the starting index of an opening bracket for which we want to find a matching closing bracket. It returns the index of the closing bracket.
     *
     * @param query
     * @param startingIndex
     * @return
     */
    private static Pair findAssertion(String query, int startingIndex) {
        int closingIndex = 0;
        int bracket = 0;
        boolean closingBracketFound = false;
        boolean firstOpenBracketEncountered = false;
        int walkingIndex = startingIndex;

        /*This loop tries to find the index of the first opening bracket. At the end of the loop, the walkingIndex will have this index number.*/
        while (!firstOpenBracketEncountered) {
            char c = query.charAt(walkingIndex);
            if (c == '(')
                firstOpenBracketEncountered = true;
            else {
                ++walkingIndex;
            }
        }

        startingIndex = walkingIndex;
        while (!closingBracketFound) {
            char c = query.charAt(walkingIndex);
            if (c == '(')
                ++bracket;
            else if (c == ')')
                --bracket;

            if (bracket == 0) {
                closingBracketFound = true;
                closingIndex = walkingIndex;
            }
            ++walkingIndex;
        }

        return new Pair(startingIndex, closingIndex);
    }


    /**
     * used to generate SMT formate that is executed by z3 out of the box
     *
     * @param query
     * @param z3FunDecSet
     * @return
     */


    public static String toSMT(String query, HashSet z3FunDecSet) {
        assert (query.length() > 0);

        String newQuery = new String();
        /*removing the outer solve*/
        query = query.substring(8, query.length() - 1);

        int startingIndex = 0;
        int endingIndex = query.length();
        while (startingIndex < endingIndex) {
            Pair startEndIndecies = findAssertion(query, startingIndex);

            startingIndex = (int) startEndIndecies.getFirst();
            int assertionEndIndex = (int) startEndIndecies.getSecond();

            String assertion = query.substring(startingIndex, assertionEndIndex + 1); //+1 because substring is not inclusive for the endIndex.
            newQuery += "(assert " + assertion + ")\n";
            startingIndex = assertionEndIndex + 1;
        }

        newQuery = //"  (set-logic QF_BV)\n" +
                "  (set-option :produce-unsat-cores true)\n" +
                        generateFunDec(z3FunDecSet) +
                        newQuery;


        return newQuery;
    }

    private static String generateFunDec(HashSet<String> z3FunDecSet) {
        String funDec = "";
        for (String varName : z3FunDecSet) {
            funDec = funDec + "(declare-fun " + varName + " () Int)\n";
        }
        return funDec;
    }


}
