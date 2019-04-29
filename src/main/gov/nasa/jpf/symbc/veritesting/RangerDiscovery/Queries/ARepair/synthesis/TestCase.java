package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ARepair.synthesis;

import jkind.lustre.values.Value;

import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

public class TestCase {
    //a hashmap between the testInput var name and its values in this counterExample
    HashMap<String, List<Value>> testCaseMap;

    public TestCase(HashMap<String, List<Value>> testCaseMap) {
        this.testCaseMap = testCaseMap;
    }

    public boolean isEqual(TestCase testCase) {
        if (this.testCaseMap.size() != testCase.testCaseMap.size())
            return false;
        else {// we need to do more checks to make sure that the test cases are the same.
            Set<String> myKeySet = this.testCaseMap.keySet();
            Iterator<String> keySetItr = myKeySet.iterator();
            while (keySetItr.hasNext()) {
                String var = keySetItr.next();
                if (!valuesEquals(this.testCaseMap.get(var), testCase.testCaseMap.get(var)))
                    return false;
            }
            return true;
        }
    }

    private boolean valuesEquals(List<Value> values1, List<Value> values2) {
        if(values1 != null && values2 == null) //meaning there is a mapping that isn't quite matching, because we
            // could not find the entry of a variable in the test case, then we consider the test case different.
            return false;

        if (values1.size() != values2.size())
            return false;
        else {
            for (int i = 0; i < values1.size(); i++) {
                if (!values1.get(i).equals(values2.get(i)))
                    return false;
            }
            return true;
        }
    }

    public String toString() {
        String myStr ="\n";
        for (HashMap.Entry e : testCaseMap.entrySet()) {
            String input = (String) e.getKey();
            myStr += input + ":" + e.getValue().toString()+"\n";
        }
        return myStr;
    }

}
