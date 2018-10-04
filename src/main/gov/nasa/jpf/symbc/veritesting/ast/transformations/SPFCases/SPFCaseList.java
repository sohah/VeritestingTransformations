package gov.nasa.jpf.symbc.veritesting.ast.transformations.SPFCases;

import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.SPFCaseStmt;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Operation;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;

public class SPFCaseList {
    public final HashSet<SPFCaseStmt> casesList = new HashSet<>();

    public SPFCaseList(HashSet<SPFCaseStmt> spfCaseList) {
        Iterator<SPFCaseStmt> itr = spfCaseList.iterator();
        while(itr.hasNext()){
            addCase(itr.next());
        }
    }

    public SPFCaseList() {

    }

    //we can do optimization here to check if we already had added this case before.
    public void addCase(SPFCaseStmt c) { //removes duplicated spfCases conditions
        boolean found = false;
        Iterator<SPFCaseStmt> caseItr = casesList.iterator();
        while (caseItr.hasNext() && !found) {
            if (caseItr.next().spfCondition.equals(c.spfCondition))
                found = true;
        }
        if (!found)
            casesList.add(c);
    }

    public void addAll(SPFCaseList cl) {
        casesList.addAll(cl.casesList);
    }
}