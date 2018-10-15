package gov.nasa.jpf.symbc.veritesting.VeritestingUtil;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Set;

public class StatisticManager {
    public static HashMap<String, RegionStatistics> regionsStatisticsMap = new HashMap<>();
    public static String instructionToExec;
    public static boolean veritestingRunning = false;
    public static int solverQueriesUnique = 0;
    public static boolean inializeQueriesFile = true;
    public static int hgOrdRegionInstance = 0;
    public static int SPFCaseSolverCount = 0;
    public static long SPFCaseSolverTime = 0;
    public static long constPropTime = 0;
    public static int ArraySPFCaseCount = 0;
    public static int ifRemovedCount = 0;


    public void updateVeriSuccForRegion(String key) {
        if (regionsStatisticsMap.get(key) != null) {
            RegionStatistics regionStatistics = regionsStatisticsMap.get(key);
            regionStatistics.veriHitNumber++;
        } else {
            RegionStatistics regionStatistics = new RegionStatistics(key, null, 1, 0, 0);
            regionsStatisticsMap.put(key, regionStatistics);
        }
    }

//updates the number of times we couldn't veritest a region and we left it for SPF to deal with it.
    public void updateSPFHitForRegion(String key, String failError) {
        RegionStatistics regionStatistics;
        if (regionsStatisticsMap.get(key) != null) {
            regionStatistics = regionsStatisticsMap.get(key);
            regionStatistics.spfHitNumber++;
        } else {
            regionStatistics = new RegionStatistics(key, null, 0, 1, 0);
            regionsStatisticsMap.put(key, regionStatistics);
        }

        if(failError.contains("put") || failError.contains("get")){
            regionStatistics.failReasonList.add(new FailEntry(FailEntry.FailReason.FIELDREFERNCEINSTRUCTION, failError));
        }

        else if(failError.contains("new") || (failError.contains("throw")) || (failError.contains("arrayload")) || (failError.contains("arraystore")) ){
            regionStatistics.failReasonList.add(new FailEntry(FailEntry.FailReason.SPFCASEINSTRUCTION, failError));
        }
        else{
            regionStatistics.failReasonList.add(new FailEntry(FailEntry.FailReason.OTHER, failError));
        }
    }


    public void updateConcreteHitStatForRegion(String key) {
        RegionStatistics regionStatistics;
        if (regionsStatisticsMap.get(key) != null) {
            regionStatistics = regionsStatisticsMap.get(key);
            regionStatistics.concreteNumber++;
        } else {
            regionStatistics = new RegionStatistics(key, null, 0, 0, 1);
            regionsStatisticsMap.put(key, regionStatistics);
        }
    }


    public String printAllRegionStatistics(){
        String out="\n/************************ Printing Regions Statistics *****************\n"+
        "veriHitNumber: number of times a region was successfully veritested\n" +
                "spfHitNumber: number of times we were not able to veritest a region and we left it to SPF (this is counting failures due to statements in the region we couldn't summaries.)\n" +
                "concreteHit: number of times a region was not veritested because of the condition\n" ;

        Set<String> keys = regionsStatisticsMap.keySet();
        Iterator<String> keysItr = keys.iterator();

        while(keysItr.hasNext())
            out += regionsStatisticsMap.get(keysItr.next()).print();
        return out;
    }

    public String printAccumulativeStatistics(){
        String out="\n/************************ Printing Accumulative Statistics *****************\n" +
                "Number of Distinct Veritested Regions = " + getDistinctVeriRegionNum() + "\nNumber of Distinct Un-Veritested Symbolic Regions = "+ getDistinctSpfRegionNum()
                + "\nNumber of Distinct Un-Veritested Concrete Regions = "+ getConcreteRegionNum()
                + "\nNumber of Distinct Failed Regions for Field Reference = " + getFailNum(FailEntry.FailReason.FIELDREFERNCEINSTRUCTION)
                + "\nNumber of Distinct Failed Regions for SPFCases = " + getFailNum(FailEntry.FailReason.SPFCASEINSTRUCTION)
                + "\nNumber of Distinct Failed Regions for Other Reasons = " + getFailNum(FailEntry.FailReason.OTHER)
                + "\nNumber of High Order Regions Attempted = " + hgOrdRegionInstance;
        return out;
    }

    public int getDistinctVeriRegionNum(){
        int count = 0;
        Set<String> keys = regionsStatisticsMap.keySet();
        Iterator<String> keysItr = keys.iterator();

        while(keysItr.hasNext())
            if (regionsStatisticsMap.get(keysItr.next()).veriHitNumber !=0)
                ++count;
        return count;
    }

    public int getDistinctSpfRegionNum(){
        int count = 0;
        Set<String> keys = regionsStatisticsMap.keySet();
        Iterator<String> keysItr = keys.iterator();

        while(keysItr.hasNext())
            if (regionsStatisticsMap.get(keysItr.next()).spfHitNumber !=0)
                ++count;
        return count;
    }

    public int getConcreteRegionNum(){
        int count = 0;
        Set<String> keys = regionsStatisticsMap.keySet();
        Iterator<String> keysItr = keys.iterator();

        while(keysItr.hasNext())
            if (regionsStatisticsMap.get(keysItr.next()).concreteNumber !=0)
                ++count;
        return count;
    }



    public int getFailNum(FailEntry.FailReason failReason){
        int count = 0;
        Set<String> keys = regionsStatisticsMap.keySet();
        Iterator<String> keysItr = keys.iterator();

        ArrayList<FailEntry> failReasonList;
        while(keysItr.hasNext()){
            failReasonList = regionsStatisticsMap.get(keysItr.next()).failReasonList;
            Iterator<FailEntry> failItr = failReasonList.iterator();
            Boolean failNotFound = true;
            while(failItr.hasNext() && failNotFound){
                FailEntry entry = failItr.next();
                if (entry.failReason == failReason){
                    ++count;
                    failNotFound = false;
                }
            }
        }


        return count;
    }



    public int regionCount(){
        return regionsStatisticsMap.size();
    }
}
