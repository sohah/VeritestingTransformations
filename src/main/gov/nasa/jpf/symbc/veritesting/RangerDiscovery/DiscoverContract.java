package gov.nasa.jpf.symbc.veritesting.RangerDiscovery;

import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;

import java.util.HashSet;
import java.util.LinkedHashSet;

public class DiscoverContract {

    /* This map is used to populate the spfQuery for z3, for later mainpulation. */
    public static LinkedHashSet<Pair> z3QuerySet = new LinkedHashSet();


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

    public static String generateRangerTransition(String query, HashSet z3FunDecSet) {


        String transitionHeader = generateTransitionHeader(z3FunDecSet);
        String body = generateBody(query);
        body = "(and " + body + ")";

        String rangerTransition = transitionHeader + body + ")";

        return rangerTransition;
    }

    private static String generateTransitionHeader(HashSet<String> z3FunDecSet) {
        String header = "(define-fun R (";
        String parameters = "";
        for (String varName : z3FunDecSet) {
            parameters = parameters + "(" + varName + " Int) ";
        }
        header += parameters + ") Bool\n";

        return header;
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
            constraints +=  "\t" + assertion + "\n";
            startingIndex = assertionEndIndex + 1;
        }
        return constraints;
    }



    private static String generateFunDec(HashSet<String> z3FunDecSet) {
        String funDec = "";
        for (String varName : z3FunDecSet) {
            funDec = funDec + "(declare-fun " + varName + " () Int)\n";
        }
        return funDec;
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

}
