package gov.nasa.jpf.symbc.veritesting.VeritestingUtil;

import gov.nasa.jpf.Config;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.VeritestingMain;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticRegion;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.MethodInfo;
import gov.nasa.jpf.vm.ThreadInfo;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import static gov.nasa.jpf.symbc.VeritestingListener.statisticManager;


public class JITAnalysis {
    private static HashSet<String> veriClasses = new HashSet<>();

    private static long staticAnalysisDur;
    private static boolean firstTime = true;
    private static ThreadInfo ti;
    private static Instruction instruction;
    private static VeritestingMain veritestingMain;


    /**
     * This is tries to discover statically all potential regions that could be used as veritesting regions.
     *
     * @param ti  Current running thread.
     * @param key
     */
    public static StaticRegion discoverRegions(ThreadInfo ti, Instruction instruction, String key) throws StaticRegionException {

        JITAnalysis.ti = ti;
        JITAnalysis.instruction = instruction;

        MethodInfo methodInfo = instruction.getMethodInfo();
        String className = methodInfo.getClassName();
        StaticRegion staticRegion = discoverAllClassAndGetRegion(className, key);

        statisticManager.collectStaticAnalysisMetrics(VeritestingMain.veriRegions);
        StaticRegionException.staticAnalysisComplete();
        return staticRegion;
    }

    public static StaticRegion discoverAllClassAndGetRegion(String className, String key) throws StaticRegionException {

        long startTime = System.nanoTime();

        if (firstTime) { //create veritestingMain only once.
            JITAnalysis.veritestingMain = new VeritestingMain(ti);
            firstTime = false;
        }
        if (!veriClasses.contains(className)) { // need to run static analysis first
            veriClasses.add(className);
            Config conf = ti.getVM().getConfig();
            String[] allClassPaths = conf.getStringArray("classpath");
            ArrayList<String> classPath = new ArrayList<>();
            for (String s : allClassPaths) {
                classPath.add(s);
                // These classpaths are (1) classpath in .jpf file, (2) SPF class paths, (3) JPF-core class paths, so we
                // want to run static analysis only on class paths in the .jpf file
//            if (!s.contains("jpf-symbc")) classPath.add(s);
//            else break;
            }
            //String className = conf.getString("target");

            veritestingMain.jitAnalyzeForVeritesting(classPath, className);
        }

        HashMap<String, StaticRegion> regionsMap = VeritestingMain.veriRegions;
        StaticRegion staticRegion = regionsMap.get(key);

        long endTime = System.nanoTime();
        staticAnalysisDur += endTime - startTime;

        if (staticRegion == null)
            throw new StaticRegionException("Region has no recovered static region");
        else
            return staticRegion;
    }


}
