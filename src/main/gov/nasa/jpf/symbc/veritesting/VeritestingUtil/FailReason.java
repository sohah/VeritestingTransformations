package gov.nasa.jpf.symbc.veritesting.VeritestingUtil;


public enum FailReason{
    FIELDREFERNCEINSTRUCTION,
    SPFCASEINSTRUCTION,
    CONCRETE,
    OTHER;

    public String failMsg;

    @Override
    public String toString() {
        return super.toString() + (this.failMsg == ""? "": " - FailInstruction = "+ this.failMsg.toString());
    }
}
