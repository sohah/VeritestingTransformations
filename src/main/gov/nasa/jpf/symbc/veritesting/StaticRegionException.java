package gov.nasa.jpf.symbc.veritesting;

/**
 * Exception class used whenever violation was detected during veritesting.
 */
public class StaticRegionException extends Exception {
    public StaticRegionException(String reason) {
        super(reason);
    }
}
