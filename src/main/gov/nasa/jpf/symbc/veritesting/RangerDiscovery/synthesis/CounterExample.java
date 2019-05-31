package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.synthesis;

import jkind.lustre.values.Value;

import java.util.HashMap;
import java.util.List;
import java.util.Set;

public class TestCase {
    //a hashmap between the testInput var name and its values in this counterExample
    HashMap<String, List<Value>> testCaseMap;

    public boolean isEqual(TestCase testCase){
        if(this.testCaseMap.size() != testCase.testCaseMap.size())
            return false;
        else{// we need to do more checks to make sure that the test cases are the same.
            Set<String> myKeySet = this.testCaseMap.keySet();
            while(myKeySet.iterator().hasNext()){
                String var = myKeySet.iterator().next();
                if(!valuesEquals(this.testCaseMap.get(var), testCase.testCaseMap.get(var)))
                    return false;
            }
            return true;
        }
    }

    private boolean valuesEquals(List<Value> values1, List<Value> values2) {
        if(values1.size() != values2.size())
            return false;
        else{
            for(int i=0; i<values1.size(); i++){
                if(!values1.get(i).equals(values2.get(i)))
                    return false;
            }
            return true;
        }
    }

}
