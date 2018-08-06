package gov.nasa.jpf.symbc.veritesting.ast.transformations.fieldaccess;

public class SubscriptPair {
    public Integer pathSubscript;
    public Integer globalSubscript;

    public SubscriptPair(Integer pathSubscript, Integer globalSubscript) {
        this.pathSubscript = pathSubscript;
        this.globalSubscript = globalSubscript;
    }

    @Override
    public String toString() {
        return "(" +
                "pS=" + pathSubscript +
                ", gS=" + globalSubscript +
                ')';
    }
}
