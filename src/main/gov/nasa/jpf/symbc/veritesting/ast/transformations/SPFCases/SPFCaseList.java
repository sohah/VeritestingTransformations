package gov.nasa.jpf.symbc.veritesting.ast.transformations.SPFCases;

import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.SPFCaseStmt;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Operation;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

public class SPFCaseList {
    public final HashSet<SPFCaseStmt> casesList;

    public SPFCaseList() {
        casesList = new HashSet<>();
    }

    public SPFCaseList(HashSet<SPFCaseStmt> spfCaseList) {
        casesList = spfCaseList;
    }

    //we can do optimization here to check if we already had added this case before.
    public void addCase(SPFCaseStmt c) { casesList.add(c); }

    public void addAll(SPFCaseList cl) {
        casesList.addAll(cl.casesList); }
}