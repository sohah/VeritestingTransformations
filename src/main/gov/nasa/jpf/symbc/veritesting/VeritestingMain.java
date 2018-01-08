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
import com.ibm.wala.classLoader.IBytecodeMethod;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.core.tests.callGraph.CallGraphTestUtil;
import com.ibm.wala.ipa.callgraph.AnalysisCacheImpl;
import com.ibm.wala.ipa.callgraph.AnalysisOptions;
import com.ibm.wala.ipa.callgraph.AnalysisScope;
import com.ibm.wala.ipa.callgraph.IAnalysisCacheView;
import com.ibm.wala.ipa.callgraph.impl.Everywhere;
import com.ibm.wala.ipa.cha.ClassHierarchy;
import com.ibm.wala.ipa.cha.ClassHierarchyFactory;
import com.ibm.wala.ipa.summaries.SummarizedMethod;
import com.ibm.wala.shrikeCT.InvalidClassFileException;
import com.ibm.wala.ssa.*;
import com.ibm.wala.types.MethodReference;
import com.ibm.wala.util.WalaException;
import com.ibm.wala.util.config.AnalysisScopeReader;
import com.ibm.wala.util.debug.Assertions;
import com.ibm.wala.util.graph.dominators.Dominators;
import com.ibm.wala.util.graph.dominators.NumberedDominators;
import com.ibm.wala.util.io.FileProvider;
import com.ibm.wala.util.strings.StringStuff;
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
    SSACFG cfg;
    HashSet startingPointsHistory;
    String className, methodName;
    VarUtil varUtil;
    HashSet<NatLoop> loops;
    IR ir;

    public VeritestingMain(String appJar) {
        try {
            appJar = System.getenv("TARGET_CLASSPATH_WALA") + appJar;
            AnalysisScope scope = AnalysisScopeReader.makeJavaBinaryAnalysisScope(appJar,
                    (new FileProvider()).getFile(CallGraphTestUtil.REGRESSION_EXCLUSIONS));
            cha = ClassHierarchyFactory.make(scope);
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

        try {
            File f = new File(classPath);
            URL[] cp = new URL[]{f.toURI().toURL()};
            URLClassLoader urlcl = new URLClassLoader(cp);
            className = _className;
            Class c = urlcl.loadClass(className);
            Method[] allMethods = c.getDeclaredMethods();
            for (Method m : allMethods) {
                String signature = getSignature(m);
                startAnalysis(className + "." + signature);
            }
        } catch (MalformedURLException e) {
            e.printStackTrace();
        } catch (ClassNotFoundException e) {
            e.printStackTrace();
        }
        //startAnalysis(appJar, methodSig);
    }

    public void startAnalysis(String methodSig) {
        try {
            startingPointsHistory = new HashSet();
            MethodReference mr = StringStuff.makeMethodReference(methodSig);
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
            methodName = m.getName().toString();
            System.out.println("Starting analysis for " + methodName + "(" + methodSig + ")");
            varUtil = new VarUtil(ir, className, methodName);
            NumberedDominators<ISSABasicBlock> uninverteddom =
                    (NumberedDominators<ISSABasicBlock>) Dominators.make(cfg, cfg.entry());
            loops = new HashSet<>();
            HashSet<Integer> visited = new HashSet<>();
            NatLoopSolver.findAllLoops(cfg, uninverteddom, loops, visited, cfg.getNode(0));
            doAnalysis(cfg.entry(), null);
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
            int thenUseNum, int elseUseNum) throws InvalidClassFileException {
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

        MyIVisitor myIVisitor = new MyIVisitor(varUtil, thenUseNum, elseUseNum);
        commonSucc.iterator().next().visit(myIVisitor);
        Expression phiExprSPF, finalPathExpr;
        if (myIVisitor.hasPhiExpr()) {
            phiExprSPF = myIVisitor.getPhiExprSPF(thenPLAssignSPF, elsePLAssignSPF);
            finalPathExpr =
                    new Operation(Operation.Operator.AND, pathExpr1, phiExprSPF);
        } else finalPathExpr = pathExpr1;

        int startingBC = ((IBytecodeMethod) (ir.getMethod())).getBytecodeIndex(currUnit.getLastInstructionIndex());
        int endingBC = ((IBytecodeMethod) (ir.getMethod())).getBytecodeIndex(commonSucc.getFirstInstructionIndex());

        VeritestingRegion veritestingRegion = new VeritestingRegion();
        veritestingRegion.setSummaryExpression(finalPathExpr);
        veritestingRegion.setStartInsnPosition(startingBC);
        veritestingRegion.setEndInsnPosition(endingBC);
        veritestingRegion.setOutputVars(varUtil.defLocalVars);
        veritestingRegion.setClassName(className);
        veritestingRegion.setMethodName(methodName);
        veritestingRegion.setHoleHashMap(varUtil.holeHashMap);
        if (VeritestingListener.veritestingRegions == null)
            VeritestingListener.veritestingRegions = new HashMap<String, VeritestingRegion>();

        pathLabelVarNum++;
        return veritestingRegion;
    }


    public VeritestingRegion constructMethodRegion(
            Expression summaryExp,
            ISSABasicBlock currUnit) throws InvalidClassFileException {

        int startingBC = ((IBytecodeMethod) (ir.getMethod())).getBytecodeIndex(currUnit.getLastInstructionIndex());
        int endingBC = ((IBytecodeMethod) (ir.getMethod())).getBytecodeIndex(currUnit.getLastInstructionIndex());

        VeritestingRegion veritestingRegion = new VeritestingRegion();
        veritestingRegion.setSummaryExpression(summaryExp);
        veritestingRegion.setStartInsnPosition(startingBC);
        veritestingRegion.setEndInsnPosition(endingBC);
        veritestingRegion.setOutputVars(varUtil.defLocalVars);
        veritestingRegion.setClassName(className);
        veritestingRegion.setMethodName(methodName);
        veritestingRegion.setHoleHashMap(varUtil.holeHashMap);
        if (VeritestingListener.veritestingRegions == null)
            VeritestingListener.veritestingRegions = new HashMap<String, VeritestingRegion>();
        return veritestingRegion;
    }



    public void doAnalysis(ISSABasicBlock startingUnit, ISSABasicBlock endingUnit) throws InvalidClassFileException {
        System.out.println("Starting doAnalysis");
        ISSABasicBlock currUnit = startingUnit;
        MyIVisitor myIVisitor;
        if (startingPointsHistory.contains(startingUnit)) return;
        while (true) {
            if (currUnit == null || currUnit == endingUnit) break;
            List<ISSABasicBlock> succs = new ArrayList<>(cfg.getNormalSuccessors(currUnit));
            ISSABasicBlock commonSucc = cfg.getIPdom(currUnit.getNumber());
            if (succs.size() == 1) {
                currUnit = succs.get(0);
                continue;
            } else if (succs.size() == 0)
                break;
            else if (succs.size() == 2 && startingPointsHistory.contains(currUnit)) {
                currUnit = commonSucc;
                break;
            } else if (succs.size() == 2 && !startingPointsHistory.contains(currUnit)) {
                startingPointsHistory.add(currUnit);
                varUtil.reset();

                ISSABasicBlock thenUnit = Util.getTakenSuccessor(cfg, currUnit);
                ISSABasicBlock elseUnit = Util.getNotTakenSuccessor(cfg, currUnit);
                if (isLoopStart(currUnit)) {
                    doAnalysis(thenUnit, null);
                    doAnalysis(elseUnit, null);
                    return;
                }

                Expression thenExpr = null, elseExpr = null;
                final int thenPathLabel = varUtil.getPathCounter();
                final int elsePathLabel = varUtil.getPathCounter();
                ISSABasicBlock thenPred = thenUnit, elsePred = elseUnit;
                int thenUseNum = -1, elseUseNum = -1;
                String pathLabel = "pathLabel" + pathLabelVarNum;
                final Expression thenPLAssignSPF =
                        new Operation(Operation.Operator.EQ, varUtil.makeIntermediateVar(pathLabel),
                                new IntConstant(thenPathLabel));
                final Expression elsePLAssignSPF =
                        new Operation(Operation.Operator.EQ, varUtil.makeIntermediateVar(pathLabel),
                                new IntConstant(elsePathLabel));
                boolean canVeritest = true;

                // Create thenExpr
                while (thenUnit != commonSucc) {
                    Iterator<SSAInstruction> ssaInstructionIterator = thenUnit.iterator();
                    while (ssaInstructionIterator.hasNext()) {
                        myIVisitor = new MyIVisitor(varUtil, -1, -1);
                        ssaInstructionIterator.next().visit(myIVisitor);
                        if (!myIVisitor.canVeritest()) {
                            canVeritest = false;
                            System.out.println("Cannot veritest SSAInstruction: " + myIVisitor.getLastInstruction());
                            break;
                        }
                        Expression thenExpr1 = myIVisitor.getSPFExpr();
                        if (thenExpr1 != null) {
                            if (thenExpr != null)
                                thenExpr =
                                        new Operation(Operation.Operator.AND,
                                                thenExpr, thenExpr1);
                            else thenExpr = thenExpr1;
                        }
                    }
                    if (!canVeritest) break;
                    //TODO instead of giving up, try to compute a summary of everything from thenUnit up to commonSucc
                    if (cfg.getNormalSuccessors(thenUnit).size() > 1) {
                        canVeritest = false;
                        break;
                    }
                    thenPred = thenUnit;
                    thenUnit = cfg.getNormalSuccessors(thenUnit).iterator().next();
                    if (thenUnit == endingUnit) break;
                }
                // if there is no "then" side, then set then's predecessor to currUnit
                if (canVeritest && (thenPred == commonSucc)) thenPred = currUnit;

                // Create elseExpr
                while (canVeritest && elseUnit != commonSucc) {
                    Iterator<SSAInstruction> ssaInstructionIterator = elseUnit.iterator();
                    while (ssaInstructionIterator.hasNext()) {
                        myIVisitor = new MyIVisitor(varUtil, -1, -1);
                        ssaInstructionIterator.next().visit(myIVisitor);
                        if (!myIVisitor.canVeritest()) {
                            canVeritest = false;
                            System.out.println("Cannot veritest SSAInstruction: " + myIVisitor.getLastInstruction());
                            break;
                        }
                        Expression elseExpr1 = myIVisitor.getSPFExpr();
                        if (elseExpr1 != null) {
                            if (elseExpr != null)
                                elseExpr =
                                        new Operation(Operation.Operator.AND,
                                                elseExpr, elseExpr1);
                            else elseExpr = elseExpr1;
                        }
                    }
                    if (!canVeritest) break;
                    //TODO instead of giving up, try to compute a summary of everything from elseUnit up to commonSucc
                    if (cfg.getNormalSuccessors(elseUnit).size() > 1) {
                        canVeritest = false;
                        break;
                    }
                    elsePred = elseUnit;
                    elseUnit = cfg.getNormalSuccessors(elseUnit).iterator().next();
                    if (elseUnit == endingUnit) break;
                }
                // if there is no "else" side, else set else's predecessor to currUnit
                if (canVeritest && (elsePred == commonSucc)) elsePred = currUnit;

                // Assign pathLabel a value in the elseExpr
                if (canVeritest) {
                    if (thenPred == null || elsePred == null) {
                        Assertions.UNREACHABLE("thenPred or elsePred was null");
                    }
                    thenUseNum = Util.whichPred(cfg, thenPred, commonSucc);
                    elseUseNum = Util.whichPred(cfg, elsePred, commonSucc);
                    VeritestingRegion veritestingRegion = constructVeritestingRegion(thenExpr, elseExpr,
                            thenPLAssignSPF, elsePLAssignSPF,
                            currUnit, commonSucc,
                            thenUseNum, elseUseNum);
                    if (veritestingRegion != null) {
                        /*TODO At this point we can modify the current region based on the region created for
                        the then or else side, if one of them encountered more than one successor */
                        VeritestingListener.veritestingRegions.put(
                                veritestingRegion.getClassName() + "." + veritestingRegion.getMethodName() + "#" +
                                        veritestingRegion.getStartInsnPosition(), veritestingRegion);
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

    public void doMethodAnalysis(ISSABasicBlock startingUnit, ISSABasicBlock endingUnit) throws InvalidClassFileException {
        System.out.println("Starting doAnalysis");
        ISSABasicBlock currUnit = startingUnit;
        MyIVisitor myIVisitor;
        startingPointsHistory.add(currUnit);
        varUtil.reset();

        Iterator<SSAInstruction> ssaInstructionIterator = currUnit.iterator();
        Expression summaryExp = null;
        while (ssaInstructionIterator.hasNext()) {
            myIVisitor = new MyIVisitor(varUtil, -1, -1);
            ssaInstructionIterator.next().visit(myIVisitor);
            Expression expr1 = myIVisitor.getSPFExpr();
            if (expr1 != null) {
                if (summaryExp != null)
                    summaryExp =
                            new Operation(Operation.Operator.AND,
                                    summaryExp, expr1);
                else summaryExp = expr1;
            }
        }

        VeritestingRegion veritestingRegion = constructMethodRegion(summaryExp, currUnit);
            if (veritestingRegion != null) {
                VeritestingListener.veritestingRegions.put(
                        veritestingRegion.getClassName() + "." + veritestingRegion.getMethodName() + "#" +
                                veritestingRegion.getStartInsnPosition(), veritestingRegion);
            }
    } // end doMethodAnalysis
}

