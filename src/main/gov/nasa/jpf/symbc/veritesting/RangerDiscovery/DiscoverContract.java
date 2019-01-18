package gov.nasa.jpf.symbc.veritesting.RangerDiscovery;

import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import gov.nasa.jpf.symbc.veritesting.ast.def.CloneableVariable;
import gov.nasa.jpf.symbc.veritesting.ast.def.FieldRef;
import gov.nasa.jpf.symbc.veritesting.ast.def.FieldRefVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.fieldaccess.SubscriptPair;
import gov.nasa.jpf.vm.*;
import za.ac.sun.cs.green.expr.Expression;

import java.io.BufferedWriter;
import java.io.FileOutputStream;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.util.*;

public class DiscoverContract {

    /* This map is used to populate the spfQuery for z3, for later mainpulation. */
    public static LinkedHashSet<Pair> z3QuerySet = new LinkedHashSet();

    public static String contractMethodName;

    private static ArrayList<String> contractInput = new ArrayList<>();
    private static ArrayList<String> contractOutput = new ArrayList<>();

    public static DynamicRegion dynRegion;


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

    /**
     * used to generate a transition function R for discovery of the contract of the implementation.
     *
     * @param query
     * @param z3FunDecSet
     * @param fileName
     * @return
     */
    public static String generateRangerTransition(String query, HashSet z3FunDecSet, String fileName) {

        collectOutput();
        dumpInputOutput(fileName);
        String transitionHeader = generateTransitionHeader(z3FunDecSet);
        String body = generateBody(query);
        body = "(and " + body + ")";

        String rangerTransition = transitionHeader + body + ")";

        return rangerTransition;
    }

    private static void dumpInputOutput(String fileName) {
        try (Writer writer = new BufferedWriter(new OutputStreamWriter(
                new FileOutputStream(fileName + "IN"), "utf-8"))) {
            writer.write(writeArrayList(contractInput));
        } catch (Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Error : " + e);
        }
        try (Writer writer = new BufferedWriter(new OutputStreamWriter(
                new FileOutputStream(fileName + "OUT"), "utf-8"))) {
            writer.write(writeArrayList(contractOutput));
        } catch (Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Error : " + e);
        }

    }

    private static String writeArrayList(ArrayList<String> stringArrayList) {
        String s = "";
        for (int i = 0; i < stringArrayList.size(); i++)
            s += stringArrayList.get(i) + "\n";
        return s;
    }

    private static void collectOutput() {
        for (Iterator<Map.Entry<FieldRef, SubscriptPair>> fieldRefItr = dynRegion.psm.table.entrySet().iterator();
             ((Iterator) fieldRefItr).hasNext(); ) {

            Map.Entry<FieldRef, SubscriptPair> entry = fieldRefItr.next();
            contractOutput.add((new FieldRefVarExpr(entry.getKey(), entry.getValue())).toString());
        }
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
            constraints += "\t" + assertion + "\n";
            startingIndex = assertionEndIndex + 1;
        }
        return constraints;
    }


    /**
     * used to generate the input and output of the transition function, it stores it in a file.
     * Input is defined to be the input of the method of interest plus the state of the object it lays within.
     * <p>
     * Output is defined as any state change that the method does as well as any stack slot change.
     *
     * @param dynRegion
     */
    public static void generateRInputOutput(DynamicRegion dynRegion) {


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

    public static void collectInput(ThreadInfo ti, Expression[] params, String currClassName, DynamicRegion dynRegion) {
        StackFrame sf = ti.getTopFrame();
        collectParameterInput(sf, params, dynRegion);
        collectStateInput(ti, currClassName);
    }

    private static void collectStateInput(ThreadInfo ti, String currClassName) {
        ElementInfo objRef = null;
        Iterator<ElementInfo> heapItr = ti.getHeap().iterator();

        while (objRef == null & heapItr.hasNext()) {
            ElementInfo tempObj = heapItr.next();
            if (("L" + tempObj.getClassInfo().getName() + ";").equals(currClassName))
                objRef = tempObj;
        }


        if (objRef != null) {
            FieldInfo[] declaredFields = objRef.getClassInfo().getDeclaredInstanceFields();
            for (int i = 0; i < declaredFields.length; i++) {
                Object fieldSym = objRef.getFields().getFieldAttr(i);
                //if the field has a symbolic value then this is a symbolic state of the object that should be considered as an input
                if (fieldSym != null)
                    contractInput.add(fieldSym.toString());
            }
        }
    }


    private static void collectParameterInput(StackFrame sf, Expression[] params, DynamicRegion dynRegion) {
        // for now dealing with just a single input method, to generalize I need to add this into a for loop
        int[] slot = (int[]) dynRegion.slotParamTable.lookup(params[1]);

        if (slot != null && slot.length > 0) {
            gov.nasa.jpf.symbc.numeric.Expression sym =
                    (gov.nasa.jpf.symbc.numeric.Expression) sf.getLocalAttr(slot[0]);
            if (sym != null)
                contractInput.add(sym.toString());
        }
    }
}
