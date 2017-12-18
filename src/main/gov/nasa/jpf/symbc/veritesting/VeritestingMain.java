package gov.nasa.jpf.symbc.veritesting;


/*
  Command used to copy WALA jar files to jpf-symbc/lib
  for file in `ls -l ~/git_repos/MyWALA/ | grep ^d | tr -s ' ' | cut -d ' ' -f 9 | grep -v jars | grep -v target`; do
    cp ~/git_repos/MyWALA/$file/target/*.jar ~/IdeaProjects/jpf-symbc/lib/;
  done
*/
import java.io.IOException;
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
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.ComplexNonLinearIntegerExpression;
import gov.nasa.jpf.symbc.numeric.Expression;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import x10.wala.util.NatLoop;
import x10.wala.util.NatLoopSolver;

import static gov.nasa.jpf.symbc.numeric.Comparator.EQ;
import static gov.nasa.jpf.symbc.numeric.Comparator.LOGICAL_AND;
import static gov.nasa.jpf.symbc.numeric.Comparator.LOGICAL_OR;


public class VeritestingMain {

    public int pathLabelVarNum=0;
    public HashSet endingInsnsHash;
    /*public static void main(String[] args) {
        endingInsnsHash = new HashSet();
        new MyAnalysis(args[1], args[3]);
    }*/

    public void analyzeForVeritesting(String appJar, String methodSig) {
        System.out.println(appJar + " " + methodSig);
        // causes java.lang.IllegalArgumentException: ill-formed sig testMe4(int[],int)
        endingInsnsHash = new HashSet();
        startAnalysis(appJar, methodSig);
    }

    SSACFG cfg;
    HashSet startingPointsHistory;
    String className, methodName;
    VarUtil varUtil;
    HashSet<NatLoop> loops;
    IR ir;
    public void startAnalysis(String appJar, String methodSig) {
        try {
            System.out.println("appJar = " + appJar + ", methodSig = " + methodSig);
            startingPointsHistory = new HashSet();
            appJar = System.getenv("TARGET_CLASSPATH_WALA") + appJar;
            AnalysisScope scope = AnalysisScopeReader.makeJavaBinaryAnalysisScope(appJar,
                    (new FileProvider()).getFile(CallGraphTestUtil.REGRESSION_EXCLUSIONS));
            ClassHierarchy cha = ClassHierarchyFactory.make(scope);
            MethodReference mr = StringStuff.makeMethodReference(methodSig);
            IMethod m = cha.resolveMethod(mr);
            if (m == null) {
                Assertions.UNREACHABLE("could not resolve " + mr);
            }
            AnalysisOptions options = new AnalysisOptions();
            options.getSSAOptions().setPiNodePolicy(SSAOptions.getAllBuiltInPiNodes());
            IAnalysisCacheView cache = new AnalysisCacheImpl(options.getSSAOptions());
            ir = cache.getIR(m, Everywhere.EVERYWHERE);
            if (ir == null) {
                Assertions.UNREACHABLE("Null IR for " + m);
            }
            cfg = ir.getControlFlowGraph();
            className = m.getDeclaringClass().getName().getClassName().toString();
            methodName = m.getName().toString();
            System.out.println("Starting analysis for " + methodName);
            varUtil = new VarUtil(ir, className, methodName);
            NumberedDominators<ISSABasicBlock> uninverteddom =
                    (NumberedDominators<ISSABasicBlock>) Dominators.make(cfg, cfg.entry());
            loops = new HashSet<>();
            HashSet<Integer> visited = new HashSet<>();
            NatLoopSolver.findAllLoops(cfg, uninverteddom,loops,visited,cfg.getNode(0));
            doAnalysis(cfg.entry(), null);
        } catch (WalaException|IOException |InvalidClassFileException e) {
            e.printStackTrace();
        }
    }

    public boolean isLoopStart(ISSABasicBlock b) {
        Iterator var1 = loops.iterator();

        for(int var2 = 1; var1.hasNext(); ++var2) {
            NatLoop var3 = (NatLoop)var1.next();
            if(b == var3.getStart()) return true;
        }
        return false;
    }

    public void constructVeritestingRegion(ComplexNonLinearIntegerExpression thenExpr,
                                           ComplexNonLinearIntegerExpression elseExpr,
                                           final ComplexNonLinearIntegerExpression thenPLAssignSPF,
                                           final ComplexNonLinearIntegerExpression elsePLAssignSPF,
                             //String if_SPFExpr, String ifNot_SPFExpr,
                             ISSABasicBlock currUnit, ISSABasicBlock commonSucc,
                             int thenUseNum, int elseUseNum) throws InvalidClassFileException {
        if(thenExpr != null)
            thenExpr = new ComplexNonLinearIntegerExpression(thenExpr, Comparator.LOGICAL_AND, thenPLAssignSPF);
        else thenExpr = thenPLAssignSPF;
        if(elseExpr != null)
            elseExpr = new ComplexNonLinearIntegerExpression(elseExpr, Comparator.LOGICAL_AND, elsePLAssignSPF);
        else elseExpr = elsePLAssignSPF;

        // (If && thenExpr) || (ifNot && elseExpr)
        IntegerConstant condition = new IntegerConstant(varUtil.nextInt());
        condition.setHole(true, Expression.HoleType.CONDITION);
        IntegerConstant negCondition = new IntegerConstant(varUtil.nextInt());
        negCondition.setHole(true, Expression.HoleType.NEGCONDITION);
        varUtil.holeHashMap.put(condition, condition);
        varUtil.holeHashMap.put(negCondition, negCondition);
        ComplexNonLinearIntegerExpression pathExpr1 =
                new ComplexNonLinearIntegerExpression(
                        new ComplexNonLinearIntegerExpression(condition, LOGICAL_AND, thenExpr),
                        LOGICAL_OR,
                        new ComplexNonLinearIntegerExpression(negCondition, LOGICAL_AND, elseExpr));

        MyIVisitor myIVisitor = new MyIVisitor(varUtil, thenUseNum, elseUseNum);
        commonSucc.iterator().next().visit(myIVisitor);
        ComplexNonLinearIntegerExpression phiExprSPF = myIVisitor.getPhiExprSPF(thenPLAssignSPF, elsePLAssignSPF);
        int startingBC = ((IBytecodeMethod) (ir.getMethod())).getBytecodeIndex(currUnit.getLastInstructionIndex());
        int endingBC = ((IBytecodeMethod) (ir.getMethod())).getBytecodeIndex(commonSucc.getFirstInstructionIndex());

        ComplexNonLinearIntegerExpression finalPathExpr =
                new ComplexNonLinearIntegerExpression(pathExpr1, LOGICAL_AND, phiExprSPF);

        VeritestingRegion veritestingRegion = new VeritestingRegion();
        veritestingRegion.setCNLIE(finalPathExpr);
        veritestingRegion.setStartInsnPosition(startingBC);
        veritestingRegion.setEndInsnPosition(endingBC);
        veritestingRegion.setOutputVars(varUtil.defLocalVars);
        veritestingRegion.setClassName(className);
        veritestingRegion.setMethodName(methodName);
        veritestingRegion.setHoleHashMap(varUtil.holeHashMap);
        if(VeritestingListener.veritestingRegions == null)
            VeritestingListener.veritestingRegions = new HashMap<Integer, VeritestingRegion>();
        VeritestingListener.veritestingRegions.put(startingBC, veritestingRegion);

        pathLabelVarNum++;
    }

    public void doAnalysis(ISSABasicBlock startingUnit, ISSABasicBlock endingUnit) throws InvalidClassFileException {
        System.out.println("Starting doAnalysis");
        ISSABasicBlock currUnit = startingUnit;
        MyIVisitor myIVisitor;
        if(startingPointsHistory.contains(startingUnit)) return;
        while(true) {
            if(currUnit == null || currUnit == endingUnit) break;
            //printTags((Stmt)currUnit);
            // System.out.println("BOTag = " + ((Stmt)currUnit).getTag("BytecodeOffsetTag"));
            List<ISSABasicBlock> succs = new ArrayList<>(cfg.getNormalSuccessors(currUnit));
            ISSABasicBlock commonSucc = cfg.getIPdom(currUnit.getNumber());
            if(succs.size()==1) {
                currUnit = succs.get(0);
                continue;
            } else if (succs.size()==0)
                break;
            else if(succs.size() == 2 && startingPointsHistory.contains(currUnit)) {
                currUnit = commonSucc;
                break;
            } else if(succs.size() == 2 && !startingPointsHistory.contains(currUnit)) {
                startingPointsHistory.add(currUnit);
                varUtil.reset();
                // System.out.printf("  #succs = %d\n", succs.size());
                myIVisitor = new MyIVisitor(varUtil, -1, -1);
                currUnit.getLastInstruction().visit(myIVisitor);

                ISSABasicBlock thenUnit = Util.getTakenSuccessor(cfg, currUnit);
                ISSABasicBlock elseUnit = Util.getNotTakenSuccessor(cfg, currUnit);
                if(isLoopStart(currUnit)) {
                    doAnalysis(thenUnit, null);
                    doAnalysis(elseUnit, null);
                    return;
                }

                ComplexNonLinearIntegerExpression thenExpr=null, elseExpr=null;
                final int thenPathLabel = varUtil.getPathCounter();
                final int elsePathLabel = varUtil.getPathCounter();
                ISSABasicBlock thenPred = thenUnit, elsePred = elseUnit;
                int thenUseNum=-1, elseUseNum=-1;
                String pathLabel = "pathLabel" + pathLabelVarNum;
                final ComplexNonLinearIntegerExpression thenPLAssignSPF =
                        new ComplexNonLinearIntegerExpression(varUtil.makeIntermediateVar(pathLabel), EQ,
                                new IntegerConstant(thenPathLabel));
                final ComplexNonLinearIntegerExpression elsePLAssignSPF =
                        new ComplexNonLinearIntegerExpression(varUtil.makeIntermediateVar(pathLabel), EQ,
                                new IntegerConstant(elsePathLabel));
                boolean canVeritest = true;

                // Create thenExpr
                while(thenUnit != commonSucc) {
                    // System.out.println("BOTag = " + ((Stmt)thenUnit).getTag("BytecodeOffsetTag") +
                    //     ", h.size() = " + h.size());
                    Iterator<SSAInstruction> ssaInstructionIterator = thenUnit.iterator();
                    while(ssaInstructionIterator.hasNext()) {
                        myIVisitor = new MyIVisitor(varUtil, -1, -1);
                        ssaInstructionIterator.next().visit(myIVisitor);
                        if(!myIVisitor.canVeritest()) {
                            canVeritest = false;
                            System.out.println("Cannot veritest SSAInstruction: " + myIVisitor.getLastInstruction());
                            break;
                        }
                        ComplexNonLinearIntegerExpression thenExpr1 = myIVisitor.getSPFExpr();
                        if(thenExpr1 != null) {
                            if (thenExpr != null)
                                thenExpr =
                                        new ComplexNonLinearIntegerExpression(
                                                thenExpr, LOGICAL_AND, thenExpr1);
                            else thenExpr = thenExpr1;
                        }
                    }
                    if(!canVeritest) break;
                    if(cfg.getNormalSuccessors(thenUnit).size() > 1) { canVeritest = false; break; }
                    thenPred = thenUnit;
                    thenUnit = cfg.getNormalSuccessors(thenUnit).iterator().next();
                    if(thenUnit == endingUnit) break;
                }
                // if there is no "then" side, then set then's predecessor to currUnit
                if(canVeritest && (thenPred == commonSucc)) thenPred = currUnit;

                // Create elseExpr
                while(canVeritest && elseUnit != commonSucc) {
                    // System.out.println("BOTag = " + ((Stmt)elseUnit).getTag("BytecodeOffsetTag") +
                    //     ", h.size() = " + h.size());
                    Iterator<SSAInstruction> ssaInstructionIterator = elseUnit.iterator();
                    while(ssaInstructionIterator.hasNext()) {
                        myIVisitor = new MyIVisitor(varUtil, -1, -1);
                        ssaInstructionIterator.next().visit(myIVisitor);
                        if(!myIVisitor.canVeritest()) {
                            canVeritest = false;
                            System.out.println("Cannot veritest SSAInstruction: " + myIVisitor.getLastInstruction());
                            break;
                        }
                        ComplexNonLinearIntegerExpression elseExpr1 = myIVisitor.getSPFExpr();
                        if(elseExpr1 != null) {
                            if (elseExpr != null)
                                elseExpr =
                                        new ComplexNonLinearIntegerExpression(
                                                elseExpr, LOGICAL_AND, elseExpr1);
                            else elseExpr = elseExpr1;
                        }
                    }
                    if(!canVeritest) break;
                    if(cfg.getNormalSuccessors(elseUnit).size() > 1) { canVeritest = false; break; }
                    elsePred = elseUnit;
                    elseUnit = cfg.getNormalSuccessors(elseUnit).iterator().next();
                    if(elseUnit == endingUnit) break;
                }
                // if there is no "else" side, else set else's predecessor to currUnit
                if(canVeritest && (elsePred == commonSucc)) elsePred = currUnit;

                // Assign pathLabel a value in the elseExpr
                if(canVeritest) {
                    if(thenPred == null || elsePred == null) {
                        Assertions.UNREACHABLE("thenPred or elsePred was null");
                    }
                    thenUseNum = Util.whichPred(cfg, thenPred, commonSucc);
                    elseUseNum = Util.whichPred(cfg, elsePred, commonSucc);
                    constructVeritestingRegion(thenExpr, elseExpr, thenPLAssignSPF, elsePLAssignSPF,
                            currUnit, commonSucc, thenUseNum, elseUseNum);
                }
                currUnit = commonSucc;
            } else {
                System.out.println("more than 2 successors unhandled in stmt = " + currUnit);
                assert(false);
            }
            System.out.println();
        } // end while(true)
        if(currUnit != null && currUnit != startingUnit && currUnit != endingUnit &&
                cfg.getNormalSuccessors(currUnit).size()>0) doAnalysis(currUnit, endingUnit);
    } // end doAnalysis


}

