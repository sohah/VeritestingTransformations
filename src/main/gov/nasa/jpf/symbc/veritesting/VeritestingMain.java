package gov.nasa.jpf.symbc.veritesting;


/*
  Command used to copy WALA jar files to jpf-symbc/lib
  for file in `ls -l ~/git_repos/MyWALA/ | grep ^d | tr -s ' ' | cut -d ' ' -f 9 | grep -v jars | grep -v target`; do
    cp ~/git_repos/MyWALA/$file/target/*.jar ~/IdeaProjects/jpf-symbc/lib/;
  done
*/
import java.io.File;
import java.io.IOException;
import java.lang.reflect.Method;
import java.net.MalformedURLException;
import java.net.URL;
import java.net.URLClassLoader;
import java.util.*;

import com.ibm.wala.cfg.Util;
import com.ibm.wala.classLoader.CallSiteReference;
import com.ibm.wala.classLoader.IBytecodeMethod;
import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.core.tests.callGraph.CallGraphTestUtil;
import com.ibm.wala.ipa.callgraph.AnalysisCacheImpl;
import com.ibm.wala.ipa.callgraph.AnalysisOptions;
import com.ibm.wala.ipa.callgraph.AnalysisScope;
import com.ibm.wala.ipa.callgraph.IAnalysisCacheView;
import com.ibm.wala.ipa.callgraph.impl.Everywhere;
import com.ibm.wala.ipa.cha.ClassHierarchy;
import com.ibm.wala.ipa.cha.ClassHierarchyException;
import com.ibm.wala.ipa.cha.ClassHierarchyFactory;
import com.ibm.wala.shrikeCT.InvalidClassFileException;
import com.ibm.wala.ssa.*;
import com.ibm.wala.types.MethodReference;
import com.ibm.wala.util.WalaException;
import com.ibm.wala.util.config.AnalysisScopeReader;
import com.ibm.wala.util.debug.Assertions;
import com.ibm.wala.util.graph.NumberedGraph;
import com.ibm.wala.util.graph.dominators.Dominators;
import com.ibm.wala.util.graph.dominators.NumberedDominators;
import com.ibm.wala.util.graph.impl.GraphInverter;
import com.ibm.wala.util.io.FileProvider;
import com.ibm.wala.util.strings.Atom;
import com.ibm.wala.util.strings.StringStuff;
import gov.nasa.jpf.Config;
import gov.nasa.jpf.symbc.VeritestingListener;
import x10.wala.util.NatLoop;
import x10.wala.util.NatLoopSolver;

import static gov.nasa.jpf.symbc.veritesting.ReflectUtil.getSignature;

import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.Operation;


public class VeritestingMain {

    public int pathLabelVarNum = 0;
    public HashSet endingInsnsHash;
    ClassHierarchy cha;
    HashSet<String> methodSummaryClassNames, methodSummarySubClassNames;
    private boolean methodAnalysis = false;

    public int getObjectReference() {
        return objectReference;
    }
    public void setObjectReference(int objectReference) {
        this.objectReference = objectReference;
    }
    // Relevant only if this region is a method summary
    // Used to point to the object on which the method will be called
    // Useful to get fields of the object in this method summary
    int objectReference = -1;
    SSACFG cfg;
    HashSet startingPointsHistory;
    String currentClassName, methodName, methodSig;
    VarUtil varUtil;
    HashSet<NatLoop> loops;
    IR ir;

    public VeritestingMain(String appJar) {
        try {
            appJar = System.getenv("TARGET_CLASSPATH_WALA");// + appJar;
            AnalysisScope scope = AnalysisScopeReader.makeJavaBinaryAnalysisScope(appJar,
                    (new FileProvider()).getFile(CallGraphTestUtil.REGRESSION_EXCLUSIONS));
            cha = ClassHierarchyFactory.make(scope);
            methodSummaryClassNames = new HashSet<String>();
            VeritestingListener.veritestingRegions = new HashMap<String, VeritestingRegion>();
        } catch (WalaException | IOException e) {
            e.printStackTrace();
        }
    }
    /*public static void main(String[] args) {
        endingInsnsHash = new HashSet();
        new MyAnalysis(args[1], args[3]);
    }*/

    public void analyzeForVeritesting(String classPath, String _className) {
        // causes java.lang.IllegalArgumentException: ill-formed sig testMe4(int[],int)
        endingInsnsHash = new HashSet();
        methodAnalysis = false;
        findClasses(classPath, _className);

        try {
            File f = new File(classPath);
            URL[] cp = new URL[]{f.toURI().toURL()};
            URLClassLoader urlcl = new URLClassLoader(cp);
            Class c = urlcl.loadClass(_className);
            Method[] allMethods = c.getDeclaredMethods();
            for (Method m : allMethods) {
                String signature = getSignature(m);
                startAnalysis(_className,signature);
            }
            methodSummarySubClassNames = new HashSet<String>();
            for(Iterator it = methodSummaryClassNames.iterator(); it.hasNext();) {
                String methodSummaryClassName = (String) it.next();
                Class cAdditional;
                try {
                    cAdditional = urlcl.loadClass(methodSummaryClassName);
                } catch (ClassNotFoundException e) { continue; }
                Method[] allMethodsAdditional = cAdditional.getDeclaredMethods();
                for (Method m: allMethodsAdditional) {
                    String signature = getSignature(m);
                    MethodReference mr = StringStuff.makeMethodReference(methodSummaryClassName + "." + signature);
                    IMethod iMethod = cha.resolveMethod(mr);
                    if (iMethod == null) {
                        System.out.println("could not resolve " + mr);
                        continue;
                    }
                    IClass iClass = iMethod.getDeclaringClass();
                    for(IClass subClass: cha.computeSubClasses(iClass.getReference())) {
                        if(iClass.equals(subClass)) continue;
                        methodSummarySubClassNames.add(subClass.getReference().getName().getClassName().toString());
                    }
                    //Only need to add subclass once for all the methods in the class
                    break;
                }
            }
            methodSummaryClassNames.addAll(methodSummarySubClassNames);
            for(Iterator it = methodSummaryClassNames.iterator(); it.hasNext();) {
                String methodSummaryClassName = (String) it.next();
                Class cAdditional;
                try { cAdditional = urlcl.loadClass(methodSummaryClassName); }
                catch (ClassNotFoundException e) { continue; }
                Method[] allMethodsAdditional = cAdditional.getDeclaredMethods();
                for (Method m : allMethodsAdditional) {
                    String signature = getSignature(m);
                    startAnalysis(methodSummaryClassName, signature);
                }
            }
            methodAnalysis = true;
            for(Iterator it = methodSummaryClassNames.iterator(); it.hasNext();) {
                String methodSummaryClassName = (String) it.next();
                Class cAdditional;
                try { cAdditional = urlcl.loadClass(methodSummaryClassName); }
                catch (ClassNotFoundException e) { continue; }
                Method[] allMethodsAdditional = cAdditional.getDeclaredMethods();
                for (Method m : allMethodsAdditional) {
                    String signature = getSignature(m);
                    startAnalysis(methodSummaryClassName, signature);
                }
            }
        } catch (MalformedURLException e) {
            e.printStackTrace();
        } catch (ClassNotFoundException e) {
            e.printStackTrace();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    private void findClasses(String classPath, String startingClassName) {

        methodSummaryClassNames.add(startingClassName);
        HashSet<String> newClassNames;
        do {
            newClassNames = new HashSet<>();
            for (String className : methodSummaryClassNames) {
                File f = new File(classPath);
                URL[] cp = new URL[0];
                try {
                    cp = new URL[]{f.toURI().toURL()};
                } catch (MalformedURLException e) {
                    e.printStackTrace();
                }
                URLClassLoader urlcl = new URLClassLoader(cp);
                Class c = null;
                try {
                    c = urlcl.loadClass(className);
                } catch (ClassNotFoundException e) {
                    continue;
                }
                if(c == null) continue;
                Method[] allMethods = c.getDeclaredMethods();
                for (Method method : allMethods) {
                    String signature = getSignature(method);
                    MethodReference mr = StringStuff.makeMethodReference(className + "." + signature);
                    IMethod iMethod = cha.resolveMethod(mr);
                    if(iMethod == null)
                        continue;
                    AnalysisOptions options = new AnalysisOptions();
                    options.getSSAOptions().setPiNodePolicy(SSAOptions.getAllBuiltInPiNodes());
                    IAnalysisCacheView cache = new AnalysisCacheImpl(options.getSSAOptions());
                    ir = cache.getIR(iMethod, Everywhere.EVERYWHERE);
                    Iterator<CallSiteReference> iterator = ir.iterateCallSites();
                    while (iterator.hasNext()) {
                        CallSiteReference reference = iterator.next();
                        MethodReference methodReference = reference.getDeclaredTarget();
                        String declaringClass = methodReference.getDeclaringClass().getName().getClassName().toString();
                        if (!methodSummaryClassNames.contains(declaringClass)) {
                            newClassNames.add(declaringClass);
                        }
                    }
                }
            }
            methodSummaryClassNames.addAll(newClassNames);
        } while(newClassNames.size() != 0);
    }

    public void startAnalysis(String className, String methodSig) {
        try {
            startingPointsHistory = new HashSet();
            MethodReference mr = StringStuff.makeMethodReference(className + "." + methodSig);
            IMethod m = cha.resolveMethod(mr);
            if (m == null) {
                System.out.println("could not resolve " + mr);
                return;
                //Assertions.UNREACHABLE("could not resolve " + mr);
            }
            AnalysisOptions options = new AnalysisOptions();
            options.getSSAOptions().setPiNodePolicy(SSAOptions.getAllBuiltInPiNodes());
            IAnalysisCacheView cache = new AnalysisCacheImpl(options.getSSAOptions());
            ir = cache.getIR(m, Everywhere.EVERYWHERE);
            if (ir == null) {
                Assertions.UNREACHABLE("Null IR for " + m);
            }
            cfg = ir.getControlFlowGraph();
            currentClassName = m.getDeclaringClass().getName().getClassName().toString();
            methodName = m.getName().toString();
            this.methodSig = methodSig.substring(methodSig.indexOf('('));
            System.out.println("Starting analysis for " + methodName + "(" + currentClassName + "." + methodSig + ")");
            varUtil = new VarUtil(ir, currentClassName, methodName);
            NumberedDominators<ISSABasicBlock> uninverteddom =
                    (NumberedDominators<ISSABasicBlock>) Dominators.make(cfg, cfg.entry());
            loops = new HashSet<>();
            HashSet<Integer> visited = new HashSet<>();
            NatLoopSolver.findAllLoops(cfg, uninverteddom, loops, visited, cfg.getNode(0));
            if(!methodAnalysis) doAnalysis(cfg.entry(), null);
            else doMethodAnalysis(cfg.entry(), cfg.exit());
        } catch (InvalidClassFileException e) {
            e.printStackTrace();
        }
    }

    public boolean isLoopStart(ISSABasicBlock b) {
        Iterator var1 = loops.iterator();

        while (var1.hasNext()) {
            NatLoop var3 = (NatLoop) var1.next();
            if (b == var3.getStart()) return true;
        }
        return false;
    }

    public VeritestingRegion constructVeritestingRegion(
            Expression thenExpr,
            Expression elseExpr,
            final Expression thenPLAssignSPF,
            final Expression elsePLAssignSPF,
            ISSABasicBlock currUnit, ISSABasicBlock commonSucc,
            int thenUseNum, int elseUseNum,
            HashSet<Integer> summarizedRegionStartBB) throws InvalidClassFileException {
        if (thenExpr != null)
            thenExpr = new Operation(Operation.Operator.AND, thenExpr, thenPLAssignSPF);
        else thenExpr = thenPLAssignSPF;
        if (elseExpr != null)
            elseExpr = new Operation(Operation.Operator.AND, elseExpr, elsePLAssignSPF);
        else elseExpr = elsePLAssignSPF;

        // (If && thenExpr) || (ifNot && elseExpr)
        HoleExpression condition = new HoleExpression(varUtil.nextInt());
        condition.setHole(true, HoleExpression.HoleType.CONDITION);
        HoleExpression negCondition = new HoleExpression(varUtil.nextInt());
        negCondition.setHole(true, HoleExpression.HoleType.NEGCONDITION);
        varUtil.holeHashMap.put(condition, condition);
        varUtil.holeHashMap.put(negCondition, negCondition);
        Expression pathExpr1 =
                new Operation(Operation.Operator.OR,
                        new Operation(Operation.Operator.AND, condition, thenExpr),
                        new Operation(Operation.Operator.AND, negCondition, elseExpr));

        MyIVisitor myIVisitor = new MyIVisitor(varUtil, thenUseNum, elseUseNum, true);
        //TODO there could be multiple outputs of this region, keep going until you don't find any more Phi's
        Expression phiExprSPF, finalPathExpr;
        if(commonSucc.iterator().hasNext()) {
            commonSucc.iterator().next().visit(myIVisitor);
            if (myIVisitor.hasPhiExpr()) {
                phiExprSPF = myIVisitor.getPhiExprSPF(thenPLAssignSPF, elsePLAssignSPF);
                finalPathExpr =
                        new Operation(Operation.Operator.AND, pathExpr1, phiExprSPF);
            } else finalPathExpr = pathExpr1;
        } else
            finalPathExpr = pathExpr1;

        int startingBC = ((IBytecodeMethod) (ir.getMethod())).getBytecodeIndex(currUnit.getLastInstructionIndex());
        int endingBC = ((IBytecodeMethod) (ir.getMethod())).getBytecodeIndex(commonSucc.getFirstInstructionIndex());

        VeritestingRegion veritestingRegion = new VeritestingRegion();
        veritestingRegion.setSummaryExpression(finalPathExpr);
        veritestingRegion.setStartInsnPosition(startingBC);
        veritestingRegion.setEndInsnPosition(endingBC);
        HashSet<Expression> hashSet = new HashSet<>();
        for(Expression e: varUtil.defLocalVars) {
            hashSet.add(e);
        }
        veritestingRegion.setOutputVars(hashSet);
        veritestingRegion.setClassName(currentClassName);
        veritestingRegion.setMethodName(methodName);
        veritestingRegion.setMethodSignature(methodSig);
        veritestingRegion.setStartBBNum(currUnit.getNumber());
        veritestingRegion.setEndBBNum(commonSucc.getNumber());
        HashMap<Expression, Expression> hashMap = new HashMap<>();
        for(Map.Entry<Expression, Expression> entry: varUtil.holeHashMap.entrySet()) {
            hashMap.put(entry.getKey(), entry.getValue());
        }
        veritestingRegion.setHoleHashMap(hashMap);
        veritestingRegion.setSummarizedRegionStartBB(summarizedRegionStartBB);

        pathLabelVarNum++;
        return veritestingRegion;
    }

    public void doAnalysis(ISSABasicBlock startingUnit, ISSABasicBlock endingUnit) throws InvalidClassFileException {
        //System.out.println("Starting doAnalysis");
        ISSABasicBlock currUnit = startingUnit;
        if (startingPointsHistory.contains(startingUnit)) return;
        Expression methodExpression = null;
        HashSet<Integer> methodSummarizedRegionStartBB = new HashSet<>();
        while (true) {
            if (currUnit == null || currUnit == endingUnit) break;
            List<ISSABasicBlock> succs = new ArrayList<>(cfg.getNormalSuccessors(currUnit));
            ISSABasicBlock commonSucc = cfg.getIPdom(currUnit.getNumber());
            if (succs.size() == 1) {
                if(succs.size() == 0) break;
                currUnit = succs.get(0);
                continue;
            } else if (succs.size() == 0) break;
            else if (succs.size() == 2 && startingPointsHistory.contains(currUnit)) {
                currUnit = commonSucc;
                break;
            } else if (succs.size() == 2 && !startingPointsHistory.contains(currUnit)) {
                startingPointsHistory.add(currUnit);
                //fix this varUtil reset because it screws up varUtil.holeHashMap
                varUtil.reset();

                ISSABasicBlock thenUnit = Util.getTakenSuccessor(cfg, currUnit);
                ISSABasicBlock elseUnit = Util.getNotTakenSuccessor(cfg, currUnit);
                if (isLoopStart(currUnit)) {
                    doAnalysis(thenUnit, null);
                    doAnalysis(elseUnit, null);
                    return;
                }

                Expression thenExpr = null, elseExpr = null;
                String pathLabelString = "pathLabel" + varUtil.getPathCounter();
                final int thenPathLabel = varUtil.getPathCounter();
                final int elsePathLabel = varUtil.getPathCounter();
                ISSABasicBlock thenPred = thenUnit, elsePred = elseUnit;
                int thenUseNum = -1, elseUseNum = -1;
                Expression pathLabel = varUtil.makeIntermediateVar(pathLabelString);
                final Expression thenPLAssignSPF =
                        new Operation(Operation.Operator.EQ, pathLabel,
                                new IntConstant(thenPathLabel));
                final Expression elsePLAssignSPF =
                        new Operation(Operation.Operator.EQ, pathLabel,
                                new IntConstant(elsePathLabel));
                boolean canVeritest = true;
                HashSet<Integer> summarizedRegionStartBB = new HashSet<>();
                summarizedRegionStartBB.add(currUnit.getNumber());

                // Create thenExpr
                while (thenUnit != commonSucc) {
                    boolean isPhithenUnit = false;
                    while(cfg.getNormalSuccessors(thenUnit).size() > 1 && thenUnit != commonSucc && canVeritest) {
                        if (VeritestingListener.veritestingMode == 1) {
                            canVeritest = false;
                            break;
                        }
                        assert(VeritestingListener.veritestingMode == 2 || VeritestingListener.veritestingMode == 3);
                        //instead of giving up, try to compute a summary of everything from thenUnit up to commonSucc
                        //to allow complex regions
                        HashMap<Expression, Expression> savedHoleHashMap = saveHoleHashMap();
                        HashMap<String, Expression> savedVarCache = saveVarCache();
                        doAnalysis(thenUnit, commonSucc);
                        for(Map.Entry<Expression, Expression> entry: savedHoleHashMap.entrySet()) {
                            varUtil.holeHashMap.put(entry.getKey(), entry.getValue());
                        }
                        for(Map.Entry<String, Expression> entry: savedVarCache.entrySet()) {
                            varUtil.varCache.put(entry.getKey(), entry.getValue());
                        }
                        int offset = ((IBytecodeMethod) (ir.getMethod())).getBytecodeIndex(thenUnit.getLastInstructionIndex());
                        String key = currentClassName + "." + methodName + methodSig + "#" + offset;
                        if(VeritestingListener.veritestingRegions.containsKey(key)) {
                            System.out.println("Veritested inner region with key = " + key);
                            //visit all instructions up to and including the condition
                            BlockSummary blockSummary = new BlockSummary(thenUnit, thenExpr, canVeritest, isPhithenUnit).invoke();
                            canVeritest = blockSummary.isCanVeritest();
                            thenExpr = blockSummary.getExpression();
                            Expression conditionExpression = blockSummary.getIfExpression();
                            //cannot handle returns inside a if-then-else
                            if(blockSummary.getIsExitNode()) canVeritest = false;
                            if(!canVeritest) break;
                            ISSABasicBlock commonSuccthenUnit = cfg.getIPdom(thenUnit.getNumber());

                            NumberedGraph<ISSABasicBlock> invertedCFG = GraphInverter.invert(cfg);
                            NumberedDominators<ISSABasicBlock> postDom = (NumberedDominators<ISSABasicBlock>)
                                    Dominators.make(invertedCFG, cfg.exit());
                            boolean bPostDom = (postDom.isDominatedBy(commonSuccthenUnit, commonSucc));
                            assert(bPostDom);


                            VeritestingRegion innerRegion = VeritestingListener.veritestingRegions.get(key);
                            for(Expression e: innerRegion.getOutputVars()) {
                                varUtil.defLocalVars.add(e);
                            }
                            for(Map.Entry<Expression, Expression> entry: innerRegion.getHoleHashMap().entrySet()) {
                                varUtil.holeHashMap.put(entry.getKey(), entry.getValue());
                                if(((HoleExpression)entry.getKey()).getHoleType() == HoleExpression.HoleType.CONDITION ||
                                        ((HoleExpression)entry.getKey()).getHoleType() == HoleExpression.HoleType.NEGCONDITION)
                                    varUtil.holeHashMap.remove(entry.getKey());
                            }
                            Expression thenExpr1 = innerRegion.getSummaryExpression();
                            thenExpr1 = replaceCondition(thenExpr1, conditionExpression);
                            if (thenExpr1 != null) {
                                if (thenExpr != null)
                                    thenExpr =
                                            new Operation(Operation.Operator.AND,
                                                    thenExpr, thenExpr1);
                                else thenExpr = thenExpr1;
                            }
                            thenPred = null;
                            thenUnit = commonSuccthenUnit;
                            isPhithenUnit = true;
                            summarizedRegionStartBB.addAll(innerRegion.summarizedRegionStartBB);
                        } else canVeritest = false;
                    }
                    if (!canVeritest || thenUnit == commonSucc) break;
                    BlockSummary blockSummary = new BlockSummary(thenUnit, thenExpr, canVeritest, isPhithenUnit).invoke();
                    canVeritest = blockSummary.isCanVeritest();
                    thenExpr = blockSummary.getExpression();
                    //we should not encounter a BB with more than one successor at this point
                    assert(blockSummary.getIfExpression() == null);
                    //cannot handle returns inside a if-then-else
                    if(blockSummary.getIsExitNode()) canVeritest = false;
                    if (!canVeritest) break;
                    thenPred = thenUnit;
                    thenUnit = cfg.getNormalSuccessors(thenUnit).iterator().next();
                    if (thenUnit == endingUnit) break;
                }
                // if there is no "then" side, then set then's predecessor to currUnit
                if (canVeritest && (thenPred == commonSucc)) thenPred = currUnit;

                //move static analysis deeper into the then-side searching for veritesting regions
                if (!canVeritest) {
                    while(thenUnit != commonSucc) {
                        if(cfg.getNormalSuccessors(thenUnit).size() > 1) {
                            doAnalysis(thenUnit, commonSucc);
                            break;
                        }
                        if(cfg.getNormalSuccessors(thenUnit).size() == 0) break;
                        thenUnit = cfg.getNormalSuccessors(thenUnit).iterator().next();
                    }
                }

                // Create elseExpr
                while (canVeritest && elseUnit != commonSucc) {
                    boolean isPhielseUnit = false;
                    while(cfg.getNormalSuccessors(elseUnit).size() > 1 && elseUnit != commonSucc && canVeritest) {
                        if (VeritestingListener.veritestingMode == 1) {
                            canVeritest = false;
                            break;
                        }
                        assert(VeritestingListener.veritestingMode == 2 || VeritestingListener.veritestingMode == 3);
                        //instead of giving up, try to compute a summary of everything from elseUnit up to commonSucc
                        //to allow complex regions
                        HashMap<Expression, Expression> savedHoleHashMap = saveHoleHashMap();
                        HashMap<String, Expression> savedVarCache = saveVarCache();
                        doAnalysis(elseUnit, commonSucc);
                        for(Map.Entry<Expression, Expression> entry: savedHoleHashMap.entrySet()) {
                            varUtil.holeHashMap.put(entry.getKey(), entry.getValue());
                        }
                        for(Map.Entry<String, Expression> entry: savedVarCache.entrySet()) {
                            varUtil.varCache.put(entry.getKey(), entry.getValue());
                        }
                        int offset = ((IBytecodeMethod) (ir.getMethod())).getBytecodeIndex(elseUnit.getLastInstructionIndex());
                        String key = currentClassName + "." + methodName + methodSig + "#" + offset;
                        if(VeritestingListener.veritestingRegions.containsKey(key)) {
                            System.out.println("Veritested inner region with key = " + key);
                            //visit all instructions up to and including the condition
                            BlockSummary blockSummary = new BlockSummary(elseUnit, elseExpr, canVeritest, isPhielseUnit).invoke();
                            canVeritest = blockSummary.isCanVeritest();
                            elseExpr = blockSummary.getExpression();
                            Expression conditionExpression = blockSummary.getIfExpression();
                            //cannot handle returns inside a if-then-else
                            if(blockSummary.getIsExitNode()) canVeritest = false;
                            if(!canVeritest) break;
                            ISSABasicBlock commonSuccelseUnit = cfg.getIPdom(elseUnit.getNumber());

                            if(!VeritestingListener.boostPerf) {
                                NumberedGraph<ISSABasicBlock> invertedCFG = GraphInverter.invert(cfg);
                                NumberedDominators<ISSABasicBlock> postDom = (NumberedDominators<ISSABasicBlock>)
                                        Dominators.make(invertedCFG, cfg.exit());
                                boolean bPostDom = (postDom.isDominatedBy(commonSuccelseUnit, commonSucc));
                                assert (bPostDom);
                            }


                            VeritestingRegion innerRegion = VeritestingListener.veritestingRegions.get(key);
                            for(Expression e: innerRegion.getOutputVars()) {
                                varUtil.defLocalVars.add(e);
                            }
                            for(Map.Entry<Expression, Expression> entry: innerRegion.getHoleHashMap().entrySet()) {
                                varUtil.holeHashMap.put(entry.getKey(), entry.getValue());
                                if(((HoleExpression)entry.getKey()).getHoleType() == HoleExpression.HoleType.CONDITION ||
                                        ((HoleExpression)entry.getKey()).getHoleType() == HoleExpression.HoleType.NEGCONDITION)
                                    varUtil.holeHashMap.remove(entry.getKey());
                            }
                            Expression elseExpr1 = innerRegion.getSummaryExpression();
                            elseExpr1 = replaceCondition(elseExpr1, conditionExpression);
                            if (elseExpr1 != null) {
                                if (elseExpr != null)
                                    elseExpr =
                                            new Operation(Operation.Operator.AND,
                                                    elseExpr, elseExpr1);
                                else elseExpr = elseExpr1;
                            }
                            elsePred = null;
                            elseUnit = commonSuccelseUnit;
                            isPhielseUnit = true;
                            summarizedRegionStartBB.addAll(innerRegion.summarizedRegionStartBB);
                        } else canVeritest = false;
                    }
                    if (!canVeritest || elseUnit == commonSucc) break;
                    BlockSummary blockSummary = new BlockSummary(elseUnit, elseExpr, canVeritest, isPhielseUnit).invoke();
                    canVeritest = blockSummary.isCanVeritest();
                    elseExpr = blockSummary.getExpression();
                    //we should not encounter a BB with more than one successor at this point
                    assert(blockSummary.getIfExpression() == null);
                    //cannot handle returns inside a if-then-else
                    if(blockSummary.getIsExitNode()) canVeritest = false;
                    if (!canVeritest) break;
                    elsePred = elseUnit;
                    elseUnit = cfg.getNormalSuccessors(elseUnit).iterator().next();
                    if (elseUnit == endingUnit) break;
                }
                // if there is no "else" side, else set else's predecessor to currUnit
                if (canVeritest && (elsePred == commonSucc)) elsePred = currUnit;

                //move static analysis deeper into the else-side searching for veritesting regions
                if (!canVeritest) {
                    while(elseUnit != commonSucc) {
                        if(cfg.getNormalSuccessors(elseUnit).size() > 1) {
                            doAnalysis(elseUnit, commonSucc);
                            break;
                        }
                        if(cfg.getNormalSuccessors(elseUnit).size() == 0) break;
                        elseUnit = cfg.getNormalSuccessors(elseUnit).iterator().next();
                    }
                }

                // Assign pathLabel a value in the elseExpr
                if (canVeritest) {
                    if(thenPred != null)
                        thenUseNum = Util.whichPred(cfg, thenPred, commonSucc);
                    if(elsePred != null)
                        elseUseNum = Util.whichPred(cfg, elsePred, commonSucc);
                    VeritestingRegion veritestingRegion = constructVeritestingRegion(thenExpr, elseExpr,
                            thenPLAssignSPF, elsePLAssignSPF,
                            currUnit, commonSucc,
                            thenUseNum, elseUseNum, summarizedRegionStartBB);
                    if (veritestingRegion != null) {
                        String key = veritestingRegion.getClassName() + "." + veritestingRegion.getMethodName() +
                                veritestingRegion.getMethodSignature() + "#" +
                                veritestingRegion.getStartInsnPosition();
                        FNV1 fnv = new FNV1a64();
                        fnv.init(key);
                        long hash = fnv.getHash();
                        VeritestingListener.veritestingRegions.put(key, veritestingRegion);
                    }
                }
                currUnit = commonSucc;
            } else {
                System.out.println("more than 2 successors unhandled in stmt = " + currUnit);
                assert (false);
            }
            System.out.println();
        } // end while(true)
        if (currUnit != null && currUnit != startingUnit && currUnit != endingUnit &&
                cfg.getNormalSuccessors(currUnit).size() > 0) doAnalysis(currUnit, endingUnit);
    } // end doAnalysis

    private HashMap<String, Expression> saveVarCache() {
        HashMap<String, Expression> ret = new HashMap<>();
        for (Map.Entry<String, Expression> entry : varUtil.varCache.entrySet()) {
            ret.put(entry.getKey(), entry.getValue());
        }
        return ret;
    }

    private HashMap<Expression,Expression> saveHoleHashMap() {
        HashMap<Expression, Expression> ret = new HashMap<>();
        for (Map.Entry<Expression, Expression> entry : varUtil.holeHashMap.entrySet()) {
            ret.put(entry.getKey(), entry.getValue());
        }
        return ret;
    }

    // Replace all holes of type CONDITION with conditionExpression
    // Replace all holes of type NEGCONDITION with !(conditionExpression)
    private Expression replaceCondition(Expression holeExpression, Expression conditionExpression) {
        if(holeExpression instanceof HoleExpression && ((HoleExpression)holeExpression).isHole()) {
            Expression ret = holeExpression;
            if(((HoleExpression)holeExpression).getHoleType() == HoleExpression.HoleType.CONDITION)
                ret = conditionExpression;
            if(((HoleExpression)holeExpression).getHoleType() == HoleExpression.HoleType.NEGCONDITION)
                ret = new Operation(
                        negateOperator(((Operation)conditionExpression).getOperator()),
                        ((Operation) conditionExpression).getOperand(0),
                        ((Operation) conditionExpression).getOperand(1));
            return ret;
        }
        if(holeExpression instanceof Operation) {
            Operation oldOperation = (Operation) holeExpression;
            Operation newOperation = new Operation(oldOperation.getOperator(),
                    replaceCondition(oldOperation.getOperand(0), conditionExpression),
                    replaceCondition(oldOperation.getOperand(1), conditionExpression));
            return newOperation;
        }
        return holeExpression;

    }

    private Operation.Operator negateOperator(Operation.Operator operator) {
        switch(operator) {
            case NE: return Operation.Operator.EQ;
            case EQ: return Operation.Operator.NE;
            case GT: return Operation.Operator.LE;
            case GE: return Operation.Operator.LT;
            case LT: return Operation.Operator.GE;
            case LE: return Operation.Operator.GT;
            default:
                System.out.println("Don't know how to negate Green operator (" + operator + ")");
                return null;
        }
    }

    public void doMethodAnalysis(ISSABasicBlock startingUnit, ISSABasicBlock endingUnit) throws InvalidClassFileException {
        assert(methodAnalysis);
        if(VeritestingListener.veritestingMode != 3) {
            return;
        }
        //System.out.println("Starting doMethodAnalysis");
        //currUnit represents the next BB to be summarized
        ISSABasicBlock currUnit = startingUnit;
        Expression methodExpression = null;
        HashSet<Integer> methodSummarizedRegionStartBB = new HashSet<>();
        boolean canVeritestMethod = true;
        int endingBC = 0;
        while (true) {
            if(((SSACFG.BasicBlock) currUnit).getAllInstructions().size() > 0)
                endingBC = ((IBytecodeMethod) (ir.getMethod())).getBytecodeIndex(currUnit.getLastInstructionIndex());
            List<ISSABasicBlock> succs = new ArrayList<>(cfg.getNormalSuccessors(currUnit));
            ISSABasicBlock commonSucc = cfg.getIPdom(currUnit.getNumber());
            if (succs.size() == 1 || succs.size() == 0) {
                //Assuming that it would be ok to visit a BB that starts with a phi expression
                BlockSummary blockSummary = new BlockSummary(currUnit, methodExpression, canVeritestMethod, false).invoke();
                canVeritestMethod = blockSummary.isCanVeritest();
                methodExpression = blockSummary.getExpression();
                assert(blockSummary.getIfExpression() == null);
                if(!canVeritestMethod) return;
                if(blockSummary.getIsExitNode() || succs.size() == 0) {
                    VeritestingRegion veritestingRegion =
                            constructMethodRegion(methodExpression, cfg.entry().getNumber(),
                                    cfg.entry().getNumber(), methodSummarizedRegionStartBB, endingBC);
                    String key = veritestingRegion.getClassName() + "." + veritestingRegion.getMethodName() +
                            veritestingRegion.getMethodSignature() + "#" +
                            veritestingRegion.getStartInsnPosition();
                    FNV1 fnv = new FNV1a64();
                    fnv.init(key);
                    long hash = fnv.getHash();
                    VeritestingListener.veritestingRegions.put(key, veritestingRegion);
                    return;
                }
                if (!canVeritestMethod) return;
                if(succs.size() == 0) return;
                currUnit = succs.get(0);
                continue;
            }
            else if (succs.size() == 2) {
                //Summarize instructions before the condition
                BlockSummary blockSummary = new BlockSummary(currUnit, methodExpression, canVeritestMethod, false).invoke();
                canVeritestMethod = blockSummary.isCanVeritest();
                methodExpression = blockSummary.getExpression();
                Expression conditionExpression = blockSummary.getIfExpression();
                if(!canVeritestMethod) return;
                //cannot handle returns inside a if-then-else
                if(blockSummary.getIsExitNode()) return;
                int startingBC = ((IBytecodeMethod) (ir.getMethod())).getBytecodeIndex(currUnit.getLastInstructionIndex());
                String key = currentClassName + "." + methodName + methodSig + "#" + startingBC;
                if(!VeritestingListener.veritestingRegions.containsKey(key)) return;
                VeritestingRegion veritestingRegion = VeritestingListener.veritestingRegions.get(key);
                Expression summaryExpression = veritestingRegion.getSummaryExpression();
                summaryExpression = replaceCondition(summaryExpression, conditionExpression);
                assert(veritestingRegion != null);
                if(methodExpression != null) {
                    if(veritestingRegion.getSummaryExpression() != null) {
                        methodExpression = new Operation(Operation.Operator.AND, methodExpression,
                                summaryExpression);
                    }
                }
                else methodExpression = summaryExpression;
                methodSummarizedRegionStartBB.addAll(veritestingRegion.summarizedRegionStartBB);
                varUtil.defLocalVars.addAll(veritestingRegion.getOutputVars());
                for(Map.Entry<Expression, Expression> entry: veritestingRegion.getHoleHashMap().entrySet()) {
                    if(((HoleExpression)entry.getKey()).getHoleType() == HoleExpression.HoleType.CONDITION ||
                            ((HoleExpression)entry.getKey()).getHoleType() == HoleExpression.HoleType.NEGCONDITION)
                        continue;
                    varUtil.holeHashMap.put(entry.getKey(), entry.getValue());
                }
                for(HashMap.Entry<Expression, Expression> entry: veritestingRegion.getHoleHashMap().entrySet()) {
                    if(((HoleExpression)entry.getKey()).getHoleType() == HoleExpression.HoleType.CONDITION ||
                            ((HoleExpression)entry.getKey()).getHoleType() == HoleExpression.HoleType.NEGCONDITION)
                        continue;
                    HoleExpression holeExpression = (HoleExpression) entry.getKey();
                    varUtil.varCache.put(holeExpression.getHoleVarName(), holeExpression);
                }
                currUnit = commonSucc;
            } else {
                System.out.println("doMethodAnalysis: cannot summarize more than 2 successors in BB = " + currUnit);
                return;
            }
        } // end while(true)
    } // end doMethodAnalysis

    public VeritestingRegion constructMethodRegion(
            Expression summaryExp, int startBBNum, int endBBNum, HashSet<Integer> summarizedRegionStartBB,
            int endingBC) throws InvalidClassFileException {
        VeritestingRegion veritestingRegion = new VeritestingRegion();
        veritestingRegion.setSummaryExpression(summaryExp);
        veritestingRegion.setStartInsnPosition(0);
        // assuming ending instruction position is not needed for using a method summary
        veritestingRegion.setEndInsnPosition(endingBC);
        veritestingRegion.setOutputVars(varUtil.defLocalVars);
        veritestingRegion.setRetValVars(varUtil.retValVar);
        veritestingRegion.setClassName(currentClassName);
        veritestingRegion.setMethodName(methodName);
        veritestingRegion.setMethodSignature(methodSig);
        veritestingRegion.setHoleHashMap(varUtil.holeHashMap);
        veritestingRegion.setStartBBNum(startBBNum);
        veritestingRegion.setEndBBNum(endBBNum);
        veritestingRegion.setIsMethodSummary(true);
        veritestingRegion.setSummarizedRegionStartBB(summarizedRegionStartBB);
        return veritestingRegion;
    }

    private class BlockSummary {
        private ISSABasicBlock unit;
        private Expression expression;
        private Expression lastExpression;
        private boolean isExitNode = false;

        public Expression getIfExpression() {
            return ifExpression;
        }
        private Expression ifExpression = null;

        private boolean canVeritest;
        private boolean isPhiUnit;

        public BlockSummary(ISSABasicBlock thenUnit, Expression thenExpr, boolean canVeritest, boolean isPhithenUnit) {
            this.unit = thenUnit;
            this.expression = thenExpr;
            this.canVeritest = canVeritest;
            this.isPhiUnit = isPhithenUnit;
        }

        public Expression getExpression() {
            return expression;
        }

        public boolean isCanVeritest() {
            return canVeritest;
        }

        public Expression getLastExpression() {
            return lastExpression;
        }

        public BlockSummary invoke() {
            MyIVisitor myIVisitor;Iterator<SSAInstruction> ssaInstructionIterator = unit.iterator();
            if(isPhiUnit && ssaInstructionIterator.hasNext()){
                assert(ssaInstructionIterator.next() instanceof SSAPhiInstruction);
            }
            while (ssaInstructionIterator.hasNext()) {
                myIVisitor = new MyIVisitor(varUtil, -1, -1, false);
                ssaInstructionIterator.next().visit(myIVisitor);

                if (!myIVisitor.canVeritest()) {
                    canVeritest = false;
                    System.out.println("Cannot veritest SSAInstruction: " + myIVisitor.getLastInstruction());
                    break;
                }
                if(myIVisitor.isInvoke()) {
                    methodSummaryClassNames.add(myIVisitor.getInvokeClassName());
                }
                Expression expression1 = myIVisitor.getSPFExpr();
                lastExpression = expression1;
                ifExpression = myIVisitor.getIfExpr();
                if (expression1 != null) {
                    if (expression != null)
                        expression =
                                new Operation(Operation.Operator.AND,
                                        expression, expression1);
                    else expression = expression1;
                }
                if(myIVisitor.isExitNode()) {
                    isExitNode = true;
                    break;
                }
            }
            return this;
        }

        public boolean getIsExitNode() {
            return isExitNode;
        }
    }
}

