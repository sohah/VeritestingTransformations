package gov.nasa.jpf.symbc.veritesting.VeritestingUtil;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Set;

public class StatisticManager {
    public static HashMap<String, RegionStatistics> regionsStatisticsMap = new HashMap<>();
    public static String instructionToExec;
    public static boolean veritestingRunning = false;
    public static int solverQueriesUnique = 0;
    public static boolean inializeQueriesFile = true;


    public void updateHitStatForRegion(String key) {
        if (regionsStatisticsMap.get(key) != null) {
            RegionStatistics regionStatistics = regionsStatisticsMap.get(key);
            regionStatistics.hitNumber++;
        } else {
            RegionStatistics regionStatistics = new RegionStatistics(key, false, null, 1);
            regionsStatisticsMap.put(key, regionStatistics);
        }
    }

    public void updateSuccStatForRegion(String key) {
        RegionStatistics regionStatistics = regionsStatisticsMap.get(key);
        assert (regionStatistics != null);
        regionStatistics.veritested = true;
    }


    public void updateFailStatForRegion(String key, String failError) {
        RegionStatistics regionStatistics = regionsStatisticsMap.get(key);
        assert (regionStatistics != null);
        assert (!regionStatistics.veritested);
        if(failError.contains("put") || failError.contains("get")){
//            assert((regionStatistics.failReason == null) || (regionStatistics.failReason == FailReason.FIELDREFERNCEINSTRUCTION));
            regionStatistics.failReason = FailReason.FIELDREFERNCEINSTRUCTION;
        }

        else if(failError.contains("new") || (failError.contains("throw")) || (failError.contains("arrayload")) || (failError.contains("arraystore")) ){
            assert((regionStatistics.failReason == null) || (regionStatistics.failReason == FailReason.SPFCASEINSTRUCTION));
            regionStatistics.failReason = FailReason.SPFCASEINSTRUCTION;
        }
        else{
            assert((regionStatistics.failReason == null) || (regionStatistics.failReason == FailReason.OTHER));
            regionStatistics.failReason = FailReason.OTHER;
        }

        regionStatistics.failReason.failMsg = failError;
    }


    public String printAllRegionStatistics(){
        String out="\n/************************ Printing Regions Statistics *****************";
        Set<String> keys = regionsStatisticsMap.keySet();
        Iterator<String> keysItr = keys.iterator();

        while(keysItr.hasNext())
            out += regionsStatisticsMap.get(keysItr.next()).print();
        return out;
    }

    public String printAccumulativeStatistics(){
        String out="\n/************************ Printing Accumulative Statistics *****************\n" +
                "Number of Distinct Veritested Regions = " + getVeritestedNum() + "\nNumber of Distinct Un-Veritested Symbolic Regions = "+ getNotVeritestedSymNum()
                + "\nNumber of Distinct Un-Veritested Concrete Regions = "+ getNotVeritestedConcreteNum()
                + "\nNumber of Distinct Failed Regions for Field Reference = " + getFailNum(FailReason.FIELDREFERNCEINSTRUCTION)
                + "\nNumber of Distinct Failed Regions for SPFCases = " + getFailNum(FailReason.SPFCASEINSTRUCTION)
                + "\nNumber of Distinct Failed Regions for Other Reasons = " + getFailNum(FailReason.OTHER);
        return out;
    }

    public int getVeritestedNum(){
        int count = 0;
        Set<String> keys = regionsStatisticsMap.keySet();
        Iterator<String> keysItr = keys.iterator();

        while(keysItr.hasNext())
            if(regionsStatisticsMap.get(keysItr.next()).veritested)
                ++count;

        return count;
    }

    public int getNotVeritestedSymNum(){
        int count = 0;
        Set<String> keys = regionsStatisticsMap.keySet();
        Iterator<String> keysItr = keys.iterator();

        while(keysItr.hasNext()) {
            RegionStatistics regionStatistic = regionsStatisticsMap.get(keysItr.next());
            if (!regionStatistic.veritested && regionStatistic.failReason!=FailReason.CONCRETE)
                ++count;
        }
        return count;
    }

    public int getNotVeritestedConcreteNum(){
        int count = 0;
        Set<String> keys = regionsStatisticsMap.keySet();
        Iterator<String> keysItr = keys.iterator();

        while(keysItr.hasNext()) {
            RegionStatistics regionStatistic = regionsStatisticsMap.get(keysItr.next());
            if (!regionStatistic.veritested && regionStatistic.failReason==FailReason.CONCRETE)
                ++count;
        }
        return count;
    }



    public int getFailNum(FailReason failReason){
        int count = 0;
        Set<String> keys = regionsStatisticsMap.keySet();
        Iterator<String> keysItr = keys.iterator();

        while(keysItr.hasNext())
            if(regionsStatisticsMap.get(keysItr.next()).failReason == failReason)
                ++count;

        return count;
    }

    public void updateConcreteHitStatForRegion(String key) {
        if (regionsStatisticsMap.get(key) != null) {
            RegionStatistics regionStatistics = regionsStatisticsMap.get(key);
            regionStatistics.hitNumber++;
        } else {
            RegionStatistics regionStatistics = new RegionStatistics(key, false, FailReason.CONCRETE, 1);
            regionStatistics.failReason.failMsg = "";
            regionsStatisticsMap.put(key, regionStatistics);
        }
    }

    public int regionCount(){
        return regionsStatisticsMap.size();
    }
}
