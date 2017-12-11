package gov.nasa.jpf.symbc.veritesting;

public class StringUtil {
    public static final int maxSuccSteps = 10;

    public static final String nCNLIE = "\nnew ComplexNonLinearIntegerExpression(";
    public static int pathCounter=0;

    public static final int getPathCounter() { pathCounter++; return pathCounter; }

    public static final String SPFLogicalAnd(String e1, String e2) {
        return (e1 != null && e1 != "" && e2 != null && e2 != "") ? nCNLIE + e1 + ",\nLOGICAL_AND," + e2 + ")" :
                (e1 != null && e1 != "" ? e1 : e2);
    }

    public static final String SPFLogicalOr(String e1, String e2) {
        return nCNLIE + e1 + ",\nLOGICAL_OR," + e2 + ")";
    }

    /*public static final Boolean isIntegerConstant(Value v) {
        // https://stackoverflow.com/questions/5439529/determine-if-a-string-is-an-integer-in-java
        try { Integer.parseInt(v.toString()); }
        catch (NumberFormatException e) { return false; }
        catch (NullPointerException e) { return false; }
        return true;
    }*/
}
