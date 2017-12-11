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
import x10.wala.util.NatLoop;
import x10.wala.util.NatLoopSolver;


public class VeritestingMain {

    public int pathLabelVarNum=0;
    public HashSet endingInsnsHash;
    /*public static void main(String[] args) {
        endingInsnsHash = new HashSet();
        new MyAnalysis(args[1], args[3]);
    }*/

    public Hashtable<Integer,VeritestingRegion> getVeritestingRegions(String appJar, String methodSig) {
        System.out.println(appJar + " " + methodSig);
        // causes java.lang.IllegalArgumentException: ill-formed sig testMe4(int[],int)
        //startAnalysis(appJar, methodSig);
        return null;
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

    public void printSPFExpr(String thenExpr, String elseExpr,
                             final String thenPLAssignSPF, final String elsePLAssignSPF,
                             //String if_SPFExpr, String ifNot_SPFExpr,
                             ISSABasicBlock currUnit, ISSABasicBlock commonSucc,
                             int thenUseNum, int elseUseNum) throws InvalidClassFileException {
        thenExpr = StringUtil.SPFLogicalAnd(thenExpr, thenPLAssignSPF);
        elseExpr = StringUtil.SPFLogicalAnd(elseExpr, elsePLAssignSPF);

        // (If && thenExpr) || (ifNot && elseExpr)
        String pathExpr1 =
                StringUtil.SPFLogicalOr(
                        StringUtil.SPFLogicalAnd("condition", thenExpr),
                        StringUtil.SPFLogicalAnd("negCondition", elseExpr));

        String setSlotAttr = new String();
        final ArrayList<String> lhs_SB = new ArrayList();
        MyIVisitor myIVisitor = new MyIVisitor(varUtil, thenUseNum, elseUseNum);
        commonSucc.iterator().next().visit(myIVisitor);
        String phiExprSPF = myIVisitor.getPhiExprSPF(thenPLAssignSPF, elsePLAssignSPF);
        int startingBC = ((IBytecodeMethod) (ir.getMethod())).getBytecodeIndex(currUnit.getLastInstructionIndex());
        int endingBC = ((IBytecodeMethod) (ir.getMethod())).getBytecodeIndex(commonSucc.getFirstInstructionIndex());

        String finalPathExpr = StringUtil.SPFLogicalAnd(pathExpr1, phiExprSPF);
        // System.out.println("At offset = " + startingInsn +
        //     " finalPathExpr = "+finalPathExpr);
        // System.out.println("lvt.usedLocalVars.size = " + lvt.usedLocalVars.size());

        // Generate the executeInstruction listener function
        String fn = "public void " + className +
                "_" + methodName + "_VT_" + startingBC + "_" + endingBC + "\n";
        fn += " (ThreadInfo ti, Instruction instructionToExecute) {\n";
        fn += "  if(ti.getTopFrame().getPC().getPosition() == " + startingBC + " && \n";
        fn += "     ti.getTopFrame().getMethodInfo().getName().equals(\"" + methodName + "\") && \n";
        fn += "     ti.getTopFrame().getClassInfo().getName().equals(\"" + className + "\")) {\n";
        fn +=   "      StackFrame sf = ti.getTopFrame();\n" +
                "      InstructionInfo instructionInfo = new InstructionInfo(ti).invoke();\n" +
                "      Comparator trueComparator = instructionInfo.getTrueComparator();\n" +
                "      Comparator falseComparator = instructionInfo.getFalseComparator();\n" +
                "      int numOperands = instructionInfo.getNumOperands();\n" +
                "      ComplexNonLinearIntegerExpression condition = instructionInfo.getCondition();\n" +
                "      ComplexNonLinearIntegerExpression negCondition = instructionInfo.getNegCondition();\n" +
                "      if(condition == null || negCondition == null) return;\n" +
                "      PathCondition pc;\n" +
                "      pc = ((PCChoiceGenerator) ti.getVM().getSystemState().getChoiceGenerator()).getCurrentPC();\n" +
                "      PathCondition eqPC = pc.make_copy();\n" +
                "      PathCondition nePC = pc.make_copy();\n" +
                "      IntegerExpression sym_v = (IntegerExpression) sf.getOperandAttr();\n" +
                "      eqPC._addDet(trueComparator, sym_v, 0);\n" +
                "      nePC._addDet(falseComparator, sym_v, 0);\n" +
                "      boolean eqSat = eqPC.simplify();\n" +
                "      boolean neSat = nePC.simplify();\n" +
                "      if(!eqSat && !neSat) {\n" +
                "        System.out.println(\"both sides of branch at offset 11 are unsat\");\n" +
                "        assert(false);\n" +
                "      }\n" +
                "      if( (eqSat && !neSat) || (!eqSat && neSat)) {\n" +
                "        return;\n" +
                "      }\n";
        Iterator<Integer> it = varUtil.usedLocalVars.iterator();
        while(it.hasNext()) {
            Integer integer = it.next();
            int slot = varUtil.getLocalVarSlot(integer);
            if(slot!=-1) {
                fn += "      IntegerExpression v"+integer+" = (IntegerExpression) sf.getLocalAttr("+slot+");\n";
                fn += "      if (v" + integer + " == null) {\n" +
                        "        v" + integer + " = new IntegerConstant(sf.getLocalVariable(" + slot + "));\n" +
                        "      }\n";
            }
        }
        it = varUtil.intermediateVars.iterator();
        while(it.hasNext()) {
            String string = it.next().toString();
            fn += "      SymbolicInteger v" + string + " = makeSymbolicInteger(\"v" + string + "\" + pathLabelCount);\n";
        }
        it = varUtil.defLocalVars.iterator();
        while(it.hasNext()) {
            Integer integer = it.next();
            String string = integer.toString();
            setSlotAttr += "      sf.setSlotAttr(" + varUtil.getLocalVarSlot(integer) + ",  v" + string + ");\n";
            fn += "      SymbolicInteger v" + string + " = makeSymbolicInteger(\"v" + string + "\" + pathLabelCount);\n";
        }
        for(int lhs_SB_i = 0; lhs_SB_i < lhs_SB.size(); lhs_SB_i++) {
            String tmpStr = lhs_SB.get(lhs_SB_i);
            fn += "      SymbolicInteger " + tmpStr + " = makeSymbolicInteger(\"" + tmpStr + "\" + pathLabelCount);\n";
        }
        fn += "      SymbolicInteger pathLabel" + pathLabelVarNum +
                "        = makeSymbolicInteger(\"pathLabel" + pathLabelVarNum+ "\" + pathLabelCount);\n";
        fn += "      IntegerExpression cnlie = " + finalPathExpr + ";\n";
        fn += "      cnlie = constantFold(cnlie);\n" +
                "      pc._addDet(new ComplexNonLinearIntegerConstraint((ComplexNonLinearIntegerExpression) cnlie));\n";
        fn += setSlotAttr + "\n";
        fn += "      Instruction insn=instructionToExecute;\n";
        fn += "      while(insn.getPosition() != " + endingBC + ") {\n";
        fn += "        if(insn instanceof GOTO)  insn = ((GOTO) insn).getTarget();\n";
        fn += "        else insn = insn.getNext();\n";
        fn += "      }\n";
        if(!endingInsnsHash.contains(startingBC)) {
            fn += "      while(numOperands > 0) { sf.pop(); numOperands--; }\n";
        }
        fn += "      ((PCChoiceGenerator) ti.getVM().getSystemState().getChoiceGenerator()).setCurrentPC(pc);\n";
        fn += "      ti.setNextPC(insn);\n";
        fn += "      pathLabelCount+=1;\n";
        fn += "    }\n";
        fn += "  }\n";

        System.out.println(fn);
        endingInsnsHash.add(endingBC);

        varUtil.resetUsedLocalVars();
        varUtil.resetIntermediateVars();
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
                varUtil.resetUsedLocalVars();
                varUtil.resetIntermediateVars();
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

                String thenExpr="", elseExpr="";
                final int thenPathLabel = StringUtil.getPathCounter();
                final int elsePathLabel = StringUtil.getPathCounter();
                ISSABasicBlock thenPred = thenUnit, elsePred = elseUnit;
                int thenUseNum=-1, elseUseNum=-1;
                final String thenPLAssignSPF =
                        StringUtil.nCNLIE + "pathLabel" + pathLabelVarNum +
                                ", EQ, new IntegerConstant(" + thenPathLabel + "))";
                final String elsePLAssignSPF =
                        StringUtil.nCNLIE + "pathLabel" + pathLabelVarNum +
                                ", EQ, new IntegerConstant(" + elsePathLabel + "))";
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
                        String thenExpr1 = myIVisitor.getSPFExpr();
                        if(thenExpr1 != null && !thenExpr1.equals("")) {
                            if (!thenExpr.equals(""))
                                thenExpr = StringUtil.SPFLogicalAnd(thenExpr, thenExpr1);
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
                        String elseExpr1 = myIVisitor.getSPFExpr();
                        if(elseExpr1 != null && !elseExpr1.equals("")) {
                            if (!elseExpr.equals(""))
                                elseExpr = StringUtil.SPFLogicalAnd(elseExpr, elseExpr1);
                            else elseExpr = elseExpr1;
                        }
                    }
                    if(!canVeritest) break;
                    if(cfg.getNormalSuccessors(elseUnit).size() > 1) { canVeritest = false; break; }
                    elsePred = elseUnit;
                    elseUnit = cfg.getNormalSuccessors(elseUnit).iterator().next();

                    if(elseUnit == endingUnit) break;
                }
                // if there is no "else" side, then set else's predecessor to currUnit
                if(canVeritest && (elsePred == commonSucc)) elsePred = currUnit;

                // Assign pathLabel a value in the elseExpr
                if(canVeritest) {
                    if(thenPred == null || elsePred == null) {
                        Assertions.UNREACHABLE("thenPred or elsePred was null");
                    }
                    thenUseNum = Util.whichPred(cfg, thenPred, commonSucc);
                    elseUseNum = Util.whichPred(cfg, elsePred, commonSucc);
                    printSPFExpr(thenExpr, elseExpr, thenPLAssignSPF, elsePLAssignSPF,
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

