package gov.nasa.jpf.symbc.veritesting.VeritestingUtil;

public class RegionStatistics {
    public final String regionKey;
    public boolean veritested;
    public FailReason failReason;
    public int hitNumber = 0;

    public RegionStatistics(String regionKey, boolean veritested, FailReason failReason, int hitNumber){
        this.regionKey = regionKey;
        this.veritested = veritested;
        this.failReason = failReason;
        this.hitNumber = hitNumber;
    }

    public String print(){
        return ("\n*** Region Key = " + regionKey + "\n" +
        "Veritested? | hitNumber | failReason\n" + (veritested? "Yes         | ": "No          | ") + hitNumber + "  | " + failReason
        +"\n-------------------------------------------");
    }
}
