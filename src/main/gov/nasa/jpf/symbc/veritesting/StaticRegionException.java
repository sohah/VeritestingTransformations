package gov.nasa.jpf.symbc.veritesting;

import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;

import java.util.HashMap;

/**
 * Exception class used whenever violation was detected during veritesting.
 */
public class StaticRegionException extends Exception {

    // Maps each exception's message to that exception's count of how often it was thrown
    public static HashMap<String, Integer> SREMap = new HashMap<>();

    public StaticRegionException(String reason) {
        super(reason);
    }

    public static void throwException(StaticRegionException sre) throws StaticRegionException {
        countException(sre);
        throw sre;
    }

    public static void throwException(IllegalArgumentException sre) throws IllegalArgumentException {
        countException(sre);
        throw sre;
    }


    private static void countException(Exception sre) {
        if (SREMap.containsKey(sre.getMessage())) {
            Integer p = SREMap.get(sre.getMessage());
            SREMap.put(sre.getMessage(), p+1);
        } else {
            SREMap.put(sre.getMessage(), 1);
        }
    }

}
