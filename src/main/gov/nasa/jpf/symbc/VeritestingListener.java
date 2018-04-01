/*
 * Copyright (C) 2014, United States Government, as represented by the
 * Administrator of the National Aeronautics and Space Administration.
 * All rights reserved.
 *
 * Symbolic Pathfinder (jpf-symbc) is licensed under the Apache License, 
 * Version 2.0 (the "License"); you may not use this file except
 * in compliance with the License. You may obtain a copy of the License at
 * 
 *        http://www.apache.org/licenses/LICENSE-2.0. 
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and 
 * limitations under the License.
 */


package gov.nasa.jpf.symbc;


import com.ibm.wala.types.TypeReference;
import gov.nasa.jpf.Config;
import gov.nasa.jpf.JPF;
import gov.nasa.jpf.PropertyListenerAdapter;
import gov.nasa.jpf.jvm.bytecode.GOTO;
import gov.nasa.jpf.report.ConsolePublisher;
import gov.nasa.jpf.report.Publisher;
import gov.nasa.jpf.report.PublisherExtension;
import gov.nasa.jpf.symbc.numeric.*;
import gov.nasa.jpf.symbc.numeric.solvers.SolverTranslator;
import gov.nasa.jpf.symbc.veritesting.*;
import gov.nasa.jpf.vm.*;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Operation;

import java.io.PrintWriter;
import java.util.*;

public class VeritestingListener extends PropertyListenerAdapter implements PublisherExtension {

    public static HashMap<String, VeritestingRegion> veritestingRegions;
    public static HashMap<VeritestingTransition, VeritestingRegion> veritestingTransitions;


    //TODO: make these into configuration options
    public static boolean boostPerf = true;
    public static int veritestingMode = 0;

    public static long totalSolverTime = 0, z3Time = 0;
    public static long parseTime = 0;
    public static long solverAllocTime = 0;
    public static long cleanupTime = 0;
    public static int solverCount = 0;
    public static int pathLabelCount = 1;
    private long staticAnalysisTime = 0;
    public static int fieldReadAfterWrite = 0;
    public static int fieldWriteAfterWrite = 0;
    public static int fieldWriteAfterRead = 0;
    public static final boolean allowFieldReadAfterWrite = false;
    public static final boolean allowFieldWriteAfterRead = true;
    public static final boolean allowFieldWriteAfterWrite = true;
    private static int methodSummaryRWInterference = 0;

    public VeritestingListener(Config conf, JPF jpf) {
        if (conf.hasValue("veritestingMode")) {
            veritestingMode = conf.getInt("veritestingMode");
            if (veritestingMode < 0 || veritestingMode > 3) {
                System.out.println("Warning: veritestingMode should be between 0 and 3 (both 0 and 3 included)");
                System.out.println("Warning: resetting veritestingMode to 0 (aka use vanilla SPF)");
                veritestingMode = 0;
            }
        } else {
            System.out.println("* Warning: no veritestingMode specified");
            System.out.println("* Warning: set veritestingMode to 0 to use vanilla SPF with VeritestingListener");
            System.out.println("* Warning: set veritestingMode to 1 to use veritesting with simple regions");
            System.out.println("* Warning: set veritestingMode to 2 to use veritesting with complex regions");
            System.out.println("* Warning: set veritestingMode to 3 to use veritesting with complex regions and method summaries");
            System.out.println("* Warning: resetting veritestingMode to 0 (aka use vanilla SPF)");
            veritestingMode = 0;
        }
        jpf.addPublisherExtension(ConsolePublisher.class, this);
    }

    public SymbolicInteger makeSymbolicInteger(String name) {
        //return new SymbolicInteger(name, MinMax.getVarMinInt(name), MinMax.getVarMaxInt(name));
        return new SymbolicInteger(name, Integer.MIN_VALUE, Integer.MAX_VALUE);
    }

    public void executeInstruction(VM vm, ThreadInfo ti, Instruction instructionToExecute) {
        if (veritestingMode == 0) return;
        if (veritestingRegions == null) {
            discoverRegions(ti); // static analysis to discover regions
        }
        String key = generateRegionKey(ti, instructionToExecute);

        if (veritestingRegions != null && veritestingRegions.containsKey(key)) {
            VeritestingRegion region = veritestingRegions.get(key);
            VeriPCChoiceGenerator cg;
            if (!ti.isFirstStepInsn()) { // first time around
                Expression regionSummary = instantiateRegion(ti, region); // fill holes in region
                if (regionSummary == null)
                    return; //problem filling holes, abort veritesting
/*
                cg = makeVeritestingCG(region, regionSummary, ti);
                cg.setOffset(instructionToExecute.getPosition());
                cg.setMethodName(instructionToExecute.getMethodInfo().getFullName());
                ChoiceGenerator<?> currCG = (PCChoiceGenerator) ti.getVM().getSystemState().getChoiceGenerator();
                cg.setPreviousChoiceGenerator(currCG.getPreviousChoiceGenerator());
                currCG.setPreviousChoiceGenerator(cg);
*/
//                ChoiceGenerator <?> currentChoiceGenerator = ti.getVM().getSystemState().getChoiceGenerator();
                //              currentChoiceGenerator.setPreviousChoiceGenerator(cg);
                // cg.setNextChoice(0);
                //currCG.getNextChoice();
                PathCondition pc = ((PCChoiceGenerator) ti.getVM().getSystemState().getChoiceGenerator()).getCurrentPC();
                pc._addDet(new GreenConstraint(regionSummary));
                ((PCChoiceGenerator) ti.getVM().getSystemState().getChoiceGenerator()).setCurrentPC(pc);
                setupSPF(ti, instructionToExecute, region);
                return;
            }
            return;
        }
    }

    private VeriPCChoiceGenerator makeVeritestingCG(VeritestingRegion region, Expression regionSummary, ThreadInfo ti) {
        Set<VeritestingTransition> regionTransitions = getTransitionsInRegion(region);
        VeriPCChoiceGenerator cg = null;
        int gcSize = regionTransitions == null ? 1 : regionTransitions.size()+1;
        cg = new VeriPCChoiceGenerator(gcSize); //including a choice for nominal case
        setNominalTransition(ti, regionSummary, cg, region);
        setExceptionTransition(ti, regionSummary, cg, region) ;
        return cg;
    }


    private void setExceptionTransition(ThreadInfo ti, Expression regionSummary, ChoiceGenerator<?> cg, VeritestingRegion region) {
        Set<VeritestingTransition> regionTransitions = getTransitionsInRegion(region);
        PathCondition pc = ((PCChoiceGenerator) ti.getVM().getSystemState().getChoiceGenerator()).getCurrentPC();
        if (regionTransitions != null) {
            Iterator<VeritestingTransition> veritestingTransitionIterator = regionTransitions.iterator();
            int gcChoice = 1; //starting from the first choice for non-nominal choices
            while(veritestingTransitionIterator.hasNext()) {
                Expression exceptionConstraint = new Operation(Operation.Operator.AND, regionSummary, new Operation(Operation.Operator.NOT,veritestingTransitionIterator.next().transitionConstraint));
                PathCondition excepTransitionPc = pc.make_copy(); // at this point pc will have the region summary as well
                excepTransitionPc._addDet(new GreenConstraint(exceptionConstraint));
                ((VeriPCChoiceGenerator) cg).setPC(excepTransitionPc, gcChoice);
                ++gcChoice;
            }
        }
    }

    private void setNominalTransition(ThreadInfo ti, Expression regionSummary, ChoiceGenerator<?> cg, VeritestingRegion region) {
        Set<VeritestingTransition> regionTransitions = getTransitionsInRegion(region);
        Expression nominalConstraint = regionSummary;
        if (regionTransitions != null) {
            Iterator<VeritestingTransition> veritestingTransitionIterator = regionTransitions.iterator();
            while(veritestingTransitionIterator.hasNext()) {
                nominalConstraint = new Operation(Operation.Operator.AND, nominalConstraint, veritestingTransitionIterator.next().transitionConstraint);
            }
        }
        PathCondition pc = ((PCChoiceGenerator) ti.getVM().getSystemState().getChoiceGenerator()).getCurrentPC();
        PathCondition nominalTransitionPC = pc.make_copy();
        nominalTransitionPC._addDet(new GreenConstraint(nominalConstraint));
        ((VeriPCChoiceGenerator) cg).setPC(nominalTransitionPC, 0); //setting choice 0 for veritesting nominal case
    }

    private Set<VeritestingTransition> getTransitionsInRegion(VeritestingRegion region) {
        Set<VeritestingTransition> regionTransitions = new HashSet<>();

        if(veritestingTransitions != null) {
            Set<VeritestingTransition> allTransitions = veritestingTransitions.keySet();

            Iterator<VeritestingTransition> transitionIterator = allTransitions.iterator();

            while (transitionIterator.hasNext()) {
                VeritestingTransition transition = transitionIterator.next();
                VeritestingRegion transitionRegion = veritestingTransitions.get(transition);
                if (transitionRegion.equals(region))
                    regionTransitions.add(transition);
            }
        }
        return regionTransitions;
    }

    public long generateHashCode(String key) {
        FNV1 fnv = new FNV1a64();
        fnv.init(key);
        long hash = fnv.getHash();
        return hash;
    }

    private String generateRegionKey(ThreadInfo ti, Instruction instructionToExecute) {
        return ti.getTopFrame().getClassInfo().getName() + "." + ti.getTopFrame().getMethodInfo().getName() +
                ti.getTopFrame().getMethodInfo().getSignature() +
                "#" + instructionToExecute.getPosition();
    }

    private void setupSPF(ThreadInfo ti, Instruction instructionToExecute, VeritestingRegion region) {
        Instruction insn = instructionToExecute;
        while (insn.getPosition() != region.getEndInsnPosition()) {
            if (insn instanceof GOTO && (((GOTO) insn).getTarget().getPosition() <= region.getEndInsnPosition()))
                insn = ((GOTO) insn).getTarget();
            else insn = insn.getNext();
        }
        if (insn.getMnemonic().contains("store")) insn = insn.getNext();
        StackFrame modifiableTopFrame = ti.getModifiableTopFrame();
        int numOperands = 0;
        StackFrame sf = ti.getTopFrame();
        InstructionInfo instructionInfo = new InstructionInfo().invoke(sf);
        if (instructionInfo != null && !region.isMethodSummary())
            numOperands = instructionInfo.getNumOperands();

        while (numOperands > 0) {
            modifiableTopFrame.pop();
            numOperands--;
        }
        //((PCChoiceGenerator) ti.getVM().getSystemState().getChoiceGenerator()).setCurrentPC(pc);
        ti.setNextPC(insn);
        pathLabelCount += 1;
        region.usedCount++;
    }

    private Expression instantiateRegion(ThreadInfo ti, VeritestingRegion region) {
        region.ranIntoCount++;
        StackFrame sf = ti.getTopFrame();
        //System.out.println("Starting region (" + region.toString()+") at instruction " + instructionToExecute
        //+ " (pos = " + instructionToExecute.getPosition() + ")");
        InstructionInfo instructionInfo = new InstructionInfo().invoke(sf);
        if (instructionInfo == null && !region.isMethodSummary()) return null;
        PathCondition pc;
        //We've intercepted execution before any symbolic state was reached, so return
        if (!(ti.getVM().getSystemState().getChoiceGenerator() instanceof PCChoiceGenerator)) return null;
        pc = ((PCChoiceGenerator) ti.getVM().getSystemState().getChoiceGenerator()).getCurrentPC();
        if (!boostPerf && instructionInfo != null) {
            PathCondition eqPC = pc.make_copy();
            eqPC._addDet(new GreenConstraint(instructionInfo.getCondition()));
            boolean eqSat = eqPC.simplify();
            if (!eqSat) return null;
            PathCondition nePC = pc.make_copy();
            nePC._addDet(new GreenConstraint(instructionInfo.getNegCondition()));
            boolean neSat = nePC.simplify();
            if (!neSat) return null;
            if (!eqSat && !neSat) {
                System.out.println("both sides of branch at offset " + ti.getTopFrame().getPC().getPosition() + " are unsat");
                assert (false);
            }
        }
        FillHolesOutput fillHolesOutput =
                fillHoles(region, instructionInfo, sf, ti);
        if (fillHolesOutput == null || fillHolesOutput.holeHashMap == null) return null;
        Expression summaryExpression = region.getSummaryExpression();
        Expression finalSummaryExpression = summaryExpression;
        if (fillHolesOutput.additionalAST != null) {
            if (summaryExpression != null)
                finalSummaryExpression = new Operation(Operation.Operator.AND, summaryExpression, fillHolesOutput.additionalAST);
            else finalSummaryExpression = fillHolesOutput.additionalAST;
        }
        if(finalSummaryExpression == null) {
            //System.out.println("used empty region");
            //assert(false);
        }
        finalSummaryExpression = fillASTHoles(finalSummaryExpression, fillHolesOutput.holeHashMap); //not constant-folding for now

        // pc._addDet(new GreenConstraint(finalSummaryExpression));
        if (!boostPerf) {
            String finalSummaryExpressionString = ASTToString(finalSummaryExpression);
            if (!pc.simplify()) {
                System.out.println("veritesting region added unsat summary");
                assert (false);
            }
        }
        if (!populateOutputs(region.getOutputVars(), fillHolesOutput.holeHashMap, sf, ti)) {
            return null;
        }
        return finalSummaryExpression;
    }

    private void discoverRegions(ThreadInfo ti) {
        Config conf = ti.getVM().getConfig();
        String classPath = conf.getStringArray("classpath")[0] + "/";
        String className = conf.getString("target");
        // should be like VeritestingPerf.testMe4([II)V aka jvm internal format
        VeritestingMain veritestingMain = new VeritestingMain(className + ".class");
        long startTime = System.nanoTime();
        veritestingMain.analyzeForVeritesting(classPath, className);
        long endTime = System.nanoTime();
        long duration = (endTime - startTime) / 1000000; //milliseconds
        staticAnalysisTime = (endTime - startTime);
        System.out.println("veritesting analysis took " + duration + " milliseconds");
        System.out.println("Number of veritesting regions = " + veritestingRegions.size());
    }

    private String ASTToString(Expression expression) {
        if (expression instanceof Operation) {
            Operation operation = (Operation) expression;
            String str = new String();
            if (operation.getOperator().getArity() == 2)
                str = "(" + ASTToString(operation.getOperand(0)) + " " + operation.getOperator().toString() + " " +
                        ASTToString(operation.getOperand(1)) + ")";
            else if (operation.getOperator().getArity() == 1)
                str = "(" + operation.getOperator().toString() + ASTToString(operation.getOperand(0)) + ")";
            return str;
        } else
            return expression.toString();
    }

    public void publishFinished(Publisher publisher) {
        PrintWriter pw = publisher.getOut();
        publisher.publishTopicStart("VeritestingListener report (boostPerf = " + boostPerf + ", veritestingMode = " + veritestingMode + ")");
        pw.println("static analysis time = " + staticAnalysisTime/1000000);
        pw.println("totalSolverTime = " + totalSolverTime/1000000);
        pw.println("z3Time = " + z3Time/1000000);
        pw.println("parsingTime = " + parseTime/1000000);
        pw.println("solverAllocTime = " + solverAllocTime/1000000);
        pw.println("cleanupTime = " + cleanupTime/1000000);
        pw.println("solverCount = " + solverCount);
        pw.println("(fieldReadAfterWrite, fieldWriteAfterRead, fieldWriteAfterWrite = (" + fieldReadAfterWrite + ", " +
                VeritestingListener.fieldWriteAfterRead + ", " + fieldWriteAfterWrite + ")");
        pw.println("methodSummaryRWInterference = " + methodSummaryRWInterference);
        if(veritestingMode > 0) {
            pw.println("# regions = " + VeritestingListener.veritestingRegions.size());
            int maxSummarizedBranches = getMaxSummarizedBranch(false);
            ArrayList<Integer> ranIntoByBranch = new ArrayList<>();
            ArrayList<Integer> usedByBranch = new ArrayList<>();
            ranIntoByBranch.add(0);
            usedByBranch.add(0);
            for (int i = 0; i <= maxSummarizedBranches; i++) {
                ranIntoByBranch.add(0);
                usedByBranch.add(0);
                ArrayList<VeritestingRegion> regions = getRegionsForSummarizedBranchNum(i, false);
                for (int j = 0; j < regions.size(); j++) {
                    VeritestingRegion region = regions.get(j);
                    ranIntoByBranch.set(i, ranIntoByBranch.get(i) + (region.ranIntoCount != 0 ? 1 : 0));
                    usedByBranch.set(i, usedByBranch.get(i) + (region.usedCount != 0 ? 1 : 0));
                }
            }
            pw.println("# summarized branches: # regions (#run into, #used)");
            for (int i = 0; i <= maxSummarizedBranches; i++) {
                if (getRegionsForSummarizedBranchNum(i, false).size() != 0) {
                    pw.println(i + " branches: " + getRegionsForSummarizedBranchNum(i, false).size() + " (" +
                            ranIntoByBranch.get(i) + ", " + usedByBranch.get(i) + ") ");
                }
            }
            maxSummarizedBranches = getMaxSummarizedBranch(true);
            ranIntoByBranch = new ArrayList<>();
            usedByBranch = new ArrayList<>();
            ranIntoByBranch.add(0);
            usedByBranch.add(0);
            for (int i = 0; i <= maxSummarizedBranches; i++) {
                ranIntoByBranch.add(0);
                usedByBranch.add(0);
                ArrayList<VeritestingRegion> regions = getRegionsForSummarizedBranchNum(i, true);
                for (int j = 0; j < regions.size(); j++) {
                    VeritestingRegion region = regions.get(j);
                    ranIntoByBranch.set(i, ranIntoByBranch.get(i) + (region.ranIntoCount != 0 ? 1 : 0));
                    usedByBranch.set(i, usedByBranch.get(i) + (region.usedCount != 0 ? 1 : 0));
                }
            }
            pw.println("# summarized methods: # regions (#run into, #used)");
            for (int i = 0; i <= maxSummarizedBranches; i++) {
                if (getRegionsForSummarizedBranchNum(i, true).size() != 0) {
                    pw.println(i + " branches: " + getRegionsForSummarizedBranchNum(i, true).size() + " (" +
                            ranIntoByBranch.get(i) + ", " + usedByBranch.get(i) + ") ");
                }
            }
            ArrayList<String> regions = new ArrayList<>();
            for (Map.Entry<String, VeritestingRegion> entry : veritestingRegions.entrySet()) {
                regions.add(entry.getKey());
            }

            System.out.println("Sorted regions:");
            regions.sort(String::compareTo);
            for (int i = 0; i < regions.size(); i++) {
                System.out.println(regions.get(i));
            }
        }

    }

    private ArrayList<VeritestingRegion> getRegionsForSummarizedBranchNum(int numBranch, boolean methodSummary) {
        ArrayList<VeritestingRegion> ret = new ArrayList<>();
        for (Map.Entry<String, VeritestingRegion> entry : veritestingRegions.entrySet()) {
            VeritestingRegion region = entry.getValue();
            if (region.getNumBranchesSummarized() == numBranch) {
                if (!methodSummary || (methodSummary && region.isMethodSummary()))
                    ret.add(region);
            }
        }
        return ret;
    }

    private int getMaxSummarizedBranch(boolean methodSummary) {
        int maxSummarizedBranch = 0;
        for (Map.Entry<String, VeritestingRegion> entry : veritestingRegions.entrySet()) {
            VeritestingRegion region = entry.getValue();
            if (region.getNumBranchesSummarized() > maxSummarizedBranch) {
                if (!methodSummary || (methodSummary && region.isMethodSummary()))
                    maxSummarizedBranch = region.getNumBranchesSummarized();
            }
        }
        return maxSummarizedBranch;
    }

    /*
    write all outputs of the veritesting region
     */
    //TODO make this method write the outputs atomically,
    // either all of them get written or none of them do and then SPF takes over
    private boolean populateOutputs(HashSet<Expression> outputVars,
                                    LinkedHashMap<Expression, Expression> holeHashMap,
                                    StackFrame stackFrame, ThreadInfo ti) {
        Iterator iterator = outputVars.iterator();
        while (iterator.hasNext()) {
            Expression expression = (Expression) iterator.next(), finalValue;
            assert (expression instanceof HoleExpression);
            HoleExpression holeExpression = (HoleExpression) expression;
            assert (holeHashMap.containsKey(holeExpression));
            switch (holeExpression.getHoleType()) {
                case LOCAL_OUTPUT:
                    finalValue = holeHashMap.get(holeExpression);
                    stackFrame.setSlotAttr(holeExpression.getLocalStackSlot(), GreenToSPFExpression(finalValue));
                    break;
                case FIELD_OUTPUT:
                    if(holeExpression.isLatestWrite) {
                        HoleExpression.FieldInfo fieldInfo = holeExpression.getFieldInfo();
                        assert (fieldInfo != null);
                        finalValue = holeHashMap.get(fieldInfo.writeValue);
                        fillFieldHole(ti, stackFrame, fieldInfo, holeHashMap, false, GreenToSPFExpression(finalValue));
                    }
                    break;
            }
        }
        return true;
    }

    private gov.nasa.jpf.symbc.numeric.Expression GreenToSPFExpression(Expression greenExpression) {
        GreenToSPFTranslator toSPFTranslator = new GreenToSPFTranslator();
        return toSPFTranslator.translate(greenExpression);
    }

    /*
    Walk the CNLIE expression, looking for holes (which will always be at the leaf nodes), and ensure that all holes
    are filled in
     */
    private Expression fillASTHoles(Expression holeExpression,
                                    LinkedHashMap<Expression, Expression> holeHashMap) {
        if (holeExpression instanceof HoleExpression && ((HoleExpression) holeExpression).isHole()) {
            //assert(holeHashMap.containsKey(holeExpression));
            if (!holeHashMap.containsKey(holeExpression)) {
                System.out.println("fillASTHoles does not know how to fill hole " + holeExpression.toString());
                assert (false);
            }
            Expression ret = holeHashMap.get(holeExpression);
            if (ret instanceof Operation) {
                Operation oldOperation = (Operation) ret;
                Operation newOperation = new Operation(oldOperation.getOperator(),
                        fillASTHoles(oldOperation.getOperand(0), holeHashMap),
                        fillASTHoles(oldOperation.getOperand(1), holeHashMap));
                return newOperation;
            }
            return ret;
        }
        if (holeExpression instanceof Operation) {
            Operation oldOperation = (Operation) holeExpression;
            Operation newOperation = new Operation(oldOperation.getOperator(),
                    fillASTHoles(oldOperation.getOperand(0), holeHashMap),
                    fillASTHoles(oldOperation.getOperand(1), holeHashMap));
            return newOperation;
        }
        return holeExpression;
    }

    /*
    Load from local variable stack slots IntegerExpression objects and store them into holeHashMap
     */
    //if a read after write happens on a class field, the read operation should return the latest value written to
    //the field
    private FillHolesOutput fillHoles(VeritestingRegion region,
                                      InstructionInfo instructionInfo,
                                      final StackFrame stackFrame,
                                      final ThreadInfo ti) {
        LinkedHashMap<Expression, Expression> holeHashMap = region.getHoleHashMap();
        LinkedHashMap<Expression, Expression> retHoleHashMap = new LinkedHashMap<>();
        Expression additionalAST = null;
        FillNonInputHoles fillNonInputHoles =
                new FillNonInputHoles(retHoleHashMap, null, holeHashMap, instructionInfo, false);
        if (fillNonInputHoles.invoke()) return null;
        retHoleHashMap = fillNonInputHoles.retHoleHashMap;
        FillInputHoles fillInputHoles =
                new FillInputHoles(stackFrame, ti, retHoleHashMap, null, holeHashMap, false).invoke();
        if (fillInputHoles.failure()) return null;
        retHoleHashMap = fillInputHoles.retHoleHashMap;
        FillInvokeHole fillInvokeHole = new FillInvokeHole(stackFrame, ti, holeHashMap, retHoleHashMap, additionalAST).invoke();
        if (fillInvokeHole.is()) return null;
        retHoleHashMap = fillInvokeHole.getRetHoleHashMap();
        additionalAST = fillInvokeHole.getAdditionalAST();


        return new FillHolesOutput(retHoleHashMap, additionalAST);
    }

    private boolean fillArrayLoadHoles(VeritestingRegion region, LinkedHashMap<Expression, Expression> holeHashMap, InstructionInfo instructionInfo,
                                       StackFrame stackFrame, ThreadInfo ti, LinkedHashMap<Expression, Expression> retHoleHashMap) {
        for (Map.Entry<Expression, Expression> entry : holeHashMap.entrySet()) {
            Expression key = entry.getKey(), finalValueGreen;
            gov.nasa.jpf.symbc.numeric.Expression indexAttr;
            assert (key instanceof HoleExpression);
            HoleExpression keyHoleExpression = (HoleExpression) key;
            assert (keyHoleExpression.isHole());
            switch (keyHoleExpression.getHoleType()) {
                case ARRAYLOAD:
                    HoleExpression.ArrayInfoHole arrayInfoHole = keyHoleExpression.getArrayInfo();
                    indexAttr =
                            (gov.nasa.jpf.symbc.numeric.Expression) stackFrame.getLocalAttr(((HoleExpression) (arrayInfoHole.arrayIndexHole)).getLocalStackSlot());
                    switch (((HoleExpression) arrayInfoHole.arrayIndexHole).getHoleType()) {
                        case LOCAL_INPUT: //case array index is local input
                            int arrayRef = stackFrame.getLocalVariable(((HoleExpression) arrayInfoHole.arrayRefHole).getLocalStackSlot());
                            //int arrayRef = stackFrame.peek(((HoleExpression)arrayInfoHole.arrayRefHole).getLocalStackSlot());
                            ElementInfo ei = ti.getElementInfo(arrayRef);
                            int arrayLength = ((ArrayFields) ei.getFields()).arrayLength();
                            TypeReference arrayType = arrayInfoHole.arrayType;
                            String holePathLabelString = arrayInfoHole.getPathLabelString();
                            int holePathLabel = arrayInfoHole.getPathLabel();
                            Expression pathLabelConstraint = new Operation(Operation.Operator.EQ, SPFToGreenExpr(new SymbolicInteger(holePathLabelString)), new IntConstant(holePathLabel));
                            Expression inBoundConstraint = null;
                            if (indexAttr == null) //attribute is null so index is concrete
                            {
                                int indexVal = stackFrame.getLocalVariable(((HoleExpression) arrayInfoHole.arrayIndexHole).getLocalStackSlot());
                                if (indexVal < 0 || indexVal >= arrayLength) //checking concerte index is out of bound
                                    return true;
                                int value = ei.getIntElement(indexVal);
                                finalValueGreen = SPFToGreenExpr(new IntegerConstant(value));
                                retHoleHashMap.put(keyHoleExpression, finalValueGreen);
                            } else { //index is symbolic - fun starts here :)
                                finalValueGreen = SPFToGreenExpr(indexAttr);
                                Expression[] arraySymbConstraint = new Expression[arrayLength];
                                Expression arrayLoadResult = new IntVariable("arrayLoadResult", Integer.MIN_VALUE, Integer.MAX_VALUE);
                                for (int i = 0; i < arrayLength; i++) {//constructing the symbolic index constraint
                                    Expression exp1 = new Operation(Operation.Operator.EQ, finalValueGreen, new IntConstant(i));
                                    int value = ei.getIntElement(i);
                                    Expression exp2 = new Operation(Operation.Operator.EQ, arrayLoadResult, new IntConstant(value)); //loadArrayElement(ei, arrayType)
                                    arraySymbConstraint[i] = new Operation(Operation.Operator.AND, exp1, exp2);
                                }
                                inBoundConstraint = unrollGreenOrConstraint(arraySymbConstraint);
                                inBoundConstraint = new Operation(Operation.Operator.IMPLIES, pathLabelConstraint, inBoundConstraint);
                                retHoleHashMap.put(keyHoleExpression, inBoundConstraint); //covers non exception case

                                if (outOfBound(arraySymbConstraint, finalValueGreen, ti)) {//outOfBoundException is possible
                                    VeritestingTransition outOfBoundException = new VeritestingTransition(inBoundConstraint, ((HoleExpression) key).getHoleVarName(), holePathLabelString, holePathLabel);
                                    if (veritestingTransitions == null)
                                        veritestingTransitions = new HashMap<VeritestingTransition, VeritestingRegion>();
                                    veritestingTransitions.put(outOfBoundException, region); //covers exceptional case
                                }
                            }
                            break;

                        case FIELD_INPUT:
                            break;
                        default:
                            System.out.println("Array type not supported");
                            break;
                    }

                    break;
                default:
                    break;
            }
        }
        return false;
    }

    /*
    Checks if a method's holeHashMap has a read-write interference with the outer region's holeHashmap.
    The only kind of interference allowed failure a both the outer region and the method reading the same field.
     */
    private boolean hasRWInterference(LinkedHashMap<Expression, Expression> holeHashMap,
                                      LinkedHashMap<Expression, Expression> methodHoles, InvokeInfo callSiteInfo,
                                      StackFrame stackFrame) {
        for(Map.Entry<Expression, Expression> entry: methodHoles.entrySet()) {
            HoleExpression holeExpression = (HoleExpression) entry.getKey();
            if(!(holeExpression.getHoleType() == HoleExpression.HoleType.FIELD_INPUT ||
                    holeExpression.getHoleType() == HoleExpression.HoleType.FIELD_OUTPUT)) continue;
            if(holeExpression.getHoleType() == HoleExpression.HoleType.FIELD_OUTPUT) {
                if(VarUtil.fieldHasRWOperation(holeExpression, HoleExpression.HoleType.FIELD_OUTPUT, holeHashMap,
                        callSiteInfo, stackFrame) ||
                        VarUtil.fieldHasRWOperation(holeExpression, HoleExpression.HoleType.FIELD_INPUT, holeHashMap,
                                callSiteInfo, stackFrame))
                    return true;
            }
            if(holeExpression.getHoleType() == HoleExpression.HoleType.FIELD_INPUT) {
                if(VarUtil.fieldHasRWOperation(holeExpression, HoleExpression.HoleType.FIELD_OUTPUT, holeHashMap,
                        callSiteInfo, stackFrame))
                    return true;
            }
        }
        return false;
    }

    private boolean outOfBound(Expression[] arraySymbConstraint, Expression finalValueGreen, ThreadInfo ti) {
        PCChoiceGenerator lastCG = ti.getVM().getSystemState().getLastChoiceGeneratorOfType(PCChoiceGenerator.class);
        PathCondition pc;
        if (lastCG == null)
            pc = new PathCondition();
        else
            pc = ((PCChoiceGenerator) lastCG).getCurrentPC();
        Expression outOfBoundConstraint = new Operation(Operation.Operator.GE, finalValueGreen, new IntConstant(arraySymbConstraint.length));
        pc._addDet(new GreenConstraint(outOfBoundConstraint));
        return pc.simplify();
    }

    private Expression unrollGreenOrConstraint(Expression[] arraySymbConstraint) {
        assert (arraySymbConstraint != null);
        Expression unrolledConstraint = arraySymbConstraint[0];
        for (int i = 1; i < arraySymbConstraint.length; i++) {
            unrolledConstraint = new Operation(Operation.Operator.OR, arraySymbConstraint[i], unrolledConstraint);
        }
        return unrolledConstraint;
    }

    gov.nasa.jpf.symbc.numeric.Expression fillFieldHole(ThreadInfo ti, StackFrame stackFrame,
                                                        HoleExpression.FieldInfo fieldInputInfo,
                                                        LinkedHashMap<Expression, Expression> retHoleHashMap,
                                                        boolean isRead,
                                                        gov.nasa.jpf.symbc.numeric.Expression finalValue) {
        final boolean isStatic = fieldInputInfo.isStaticField;
        int objRef = -1;
        //get the object reference from fieldInputInfo.use's local stack slot if not from the call site stack slot
        int stackSlot = -1;
        if(ti.getTopFrame().getClassInfo().getName().equals(fieldInputInfo.className) &&
                ti.getTopFrame().getMethodInfo().getName().equals(fieldInputInfo.methodName))
            stackSlot = fieldInputInfo.localStackSlot;
        else {
            stackSlot = fieldInputInfo.callSiteStackSlot;
            assert(stackSlot != -1);
        }
        //this field is being loaded from an object reference that is itself a hole
        // this object reference hole should be filled already because holes are stored in a LinkedHashMap
        // that keeps holes in the order they were created while traversing the WALA IR
        if(stackSlot == -1) {
            gov.nasa.jpf.symbc.numeric.Expression objRefExpression =
                    GreenToSPFExpression(retHoleHashMap.get(fieldInputInfo.useHole));
            assert(objRefExpression instanceof IntegerConstant);
            objRef = ((IntegerConstant) objRefExpression).value();
        }
        if (!isStatic && (stackSlot != -1)) {
            objRef = stackFrame.getLocalVariable(stackSlot);
            assert(objRef != 0);
            //load the class name dynamically based on the object reference
            fieldInputInfo.className = ti.getClassInfo(objRef).getName();
        }
        if (objRef == 0) {
            System.out.println("java.lang.NullPointerException" + "referencing field '" +
                    fieldInputInfo.fieldName + "' on null object");
            assert (false);
        } else {
            ClassInfo ci;
            try {
                ci = ClassLoaderInfo.getCurrentResolvedClassInfo(fieldInputInfo.className);
            } catch (ClassInfoException e) {
                return null;
            }
            ElementInfo eiFieldOwner;
            if (!isStatic) {
                if (isRead) eiFieldOwner = ti.getElementInfo(objRef);
                else eiFieldOwner = ti.getModifiableElementInfo(objRef);
            }
            else {
                if(isRead) eiFieldOwner = ci.getStaticElementInfo();
                else eiFieldOwner = ci.getModifiableStaticElementInfo();
            }
            FieldInfo fieldInfo = null;
            if (ci != null && !isStatic)
                fieldInfo = ci.getInstanceField(fieldInputInfo.fieldName);
            if (ci != null && isStatic)
                fieldInfo = ci.getStaticField(fieldInputInfo.fieldName);
            if (fieldInfo == null) {
                System.out.println("java.lang.NoSuchFieldError" + "referencing field '" + fieldInputInfo.fieldName
                        + "' in " + eiFieldOwner);
                assert (false);
            } else {
                if(isRead) {
                    Object fieldAttr = eiFieldOwner.getFieldAttr(fieldInfo);
                    if (fieldAttr != null) {
                        return (gov.nasa.jpf.symbc.numeric.Expression) fieldAttr;
                    } else {
                        if (fieldInfo.getStorageSize() == 1) {
                            return new IntegerConstant(eiFieldOwner.get1SlotField(fieldInfo));
                        } else {
                            return new IntegerConstant(eiFieldOwner.get2SlotField(fieldInfo));
                        }
                    }
                } else {
                    int fieldSize = fieldInfo.getStorageSize();
                    if (fieldSize == 1) {
                        eiFieldOwner.set1SlotField(fieldInfo, 0); // field value should not matter (I think)
                        eiFieldOwner.setFieldAttr(fieldInfo, finalValue);
                    } else {
                        eiFieldOwner.set2SlotField(fieldInfo, 0); // field value should not matter (I think)
                        eiFieldOwner.setFieldAttr(fieldInfo, finalValue);
                    }
                }
            }
        }
        return null;
    }

    private class InstructionInfo {
        private int numOperands;
        private Operation.Operator trueComparator, falseComparator;
        private Expression condition, negCondition;

        public Expression getCondition() {
            return condition;
        }

        public Expression getNegCondition() {
            return negCondition;
        }

        public int getNumOperands() {
            return numOperands;
        }

        public Operation.Operator getTrueComparator() {
            return trueComparator;
        }

        public Operation.Operator getFalseComparator() {
            return falseComparator;
        }

        public InstructionInfo invoke(StackFrame stackFrame) {
            String mnemonic = stackFrame.getPC().getMnemonic();
            //System.out.println("mne = " + mnemonic);
            switch (mnemonic) {
                case "ifeq":
                    numOperands = 1;
                    trueComparator = Operation.Operator.EQ;
                    falseComparator = Operation.Operator.NE;
                    break;
                case "ifne":
                    trueComparator = Operation.Operator.NE;
                    falseComparator = Operation.Operator.EQ;
                    numOperands = 1;
                    break;
                case "iflt":
                    trueComparator = Operation.Operator.LT;
                    falseComparator = Operation.Operator.GE;
                    numOperands = 1;
                    break;
                case "ifle":
                    trueComparator = Operation.Operator.LE;
                    falseComparator = Operation.Operator.GT;
                    numOperands = 1;
                    break;
                case "ifgt":
                    trueComparator = Operation.Operator.GT;
                    falseComparator = Operation.Operator.LE;
                    numOperands = 1;
                    break;
                case "ifge":
                    trueComparator = Operation.Operator.GE;
                    falseComparator = Operation.Operator.LT;
                    numOperands = 1;
                    break;
                case "ifnull":
                    trueComparator = Operation.Operator.EQ;
                    falseComparator = Operation.Operator.NE;
                    numOperands = 1;
                    break;
                case "ifnonnull":
                    trueComparator = Operation.Operator.EQ;
                    falseComparator = Operation.Operator.NE;
                    numOperands = 1;
                    break;
                case "if_icmpeq":
                    trueComparator = Operation.Operator.EQ;
                    falseComparator = Operation.Operator.NE;
                    numOperands = 2;
                    break;
                case "if_icmpne":
                    trueComparator = Operation.Operator.NE;
                    falseComparator = Operation.Operator.EQ;
                    numOperands = 2;
                    break;
                case "if_icmpgt":
                    trueComparator = Operation.Operator.GT;
                    falseComparator = Operation.Operator.LE;
                    numOperands = 2;
                    break;
                case "if_icmpge":
                    trueComparator = Operation.Operator.GE;
                    falseComparator = Operation.Operator.LT;
                    numOperands = 2;
                    break;
                case "if_icmple":
                    trueComparator = Operation.Operator.LE;
                    falseComparator = Operation.Operator.GT;
                    numOperands = 2;
                    break;
                case "if_icmplt":
                    trueComparator = Operation.Operator.LT;
                    falseComparator = Operation.Operator.GE;
                    numOperands = 2;
                    break;
                default:
                    return null;
            }
            assert (numOperands == 1 || numOperands == 2);
            IntegerExpression operand1 = null, operand2 = null;
            boolean isConcreteCondition = true;
            if (numOperands == 1) {
                gov.nasa.jpf.symbc.numeric.Expression operand1_expr = (gov.nasa.jpf.symbc.numeric.Expression)
                        stackFrame.getOperandAttr();
                operand1 = (IntegerExpression) operand1_expr;
                if (operand1 == null) operand1 = new IntegerConstant(stackFrame.peek());
                else isConcreteCondition = false;
                operand2 = new IntegerConstant(0);
            }
            if (numOperands == 2) {
                operand1 = (IntegerExpression) stackFrame.getOperandAttr(1);
                if (operand1 == null) operand1 = new IntegerConstant(stackFrame.peek(1));
                else isConcreteCondition = false;
                operand2 = (IntegerExpression) stackFrame.getOperandAttr(0);
                if (operand2 == null) operand2 = new IntegerConstant(stackFrame.peek(0));
                else isConcreteCondition = false;
            }
            if (isConcreteCondition) {
                return null;
            } else {
                condition = new Operation(trueComparator, SPFToGreenExpr(operand1), SPFToGreenExpr(operand2));
                negCondition = new Operation(falseComparator, SPFToGreenExpr(operand1), SPFToGreenExpr(operand2));
            }
            return this;
        }

    }

    Expression SPFToGreenExpr(gov.nasa.jpf.symbc.numeric.Expression spfExp) {
        SolverTranslator.Translator toGreenTranslator = new SolverTranslator.Translator();
        spfExp.accept(toGreenTranslator);
        return toGreenTranslator.getExpression();
    }

    private class FillNonInputHoles {
        private final VeritestingListener.InstructionInfo instructionInfo;
        private final boolean isMethodSummary;
        private LinkedHashMap<Expression, Expression> retHoleHashMap;
        private InvokeInfo callSiteInfo;
        private LinkedHashMap<Expression, Expression> methodHoles;

        public FillNonInputHoles(LinkedHashMap<Expression, Expression> retHoleHashMap, InvokeInfo callSiteInfo,
                                 LinkedHashMap<Expression, Expression> methodHoles, InstructionInfo instructionInfo,
                                 boolean isMethodSummary) {
            this.retHoleHashMap = retHoleHashMap;
            this.callSiteInfo = callSiteInfo;
            this.methodHoles = methodHoles;
            this.instructionInfo = instructionInfo;
            this.isMethodSummary = isMethodSummary;
        }

        public boolean invoke() {
            gov.nasa.jpf.symbc.numeric.Expression spfExpr;
            Expression greenExpr;//fill all holes inside the method summary
            for(Map.Entry<Expression, Expression> entry1 : methodHoles.entrySet()) {
                Expression methodKeyExpr = entry1.getKey();
                assert(methodKeyExpr instanceof HoleExpression);
                HoleExpression methodKeyHole = (HoleExpression) methodKeyExpr;
                assert(methodKeyHole.isHole());
                switch(methodKeyHole.getHoleType()) {
                    case CONDITION:
                        if(isMethodSummary) {
                            System.out.println("unsupported condition hole in method summary");
                            return true;
                        } else {
                            assert(instructionInfo != null);
                            greenExpr = instructionInfo.getCondition();
                            assert (greenExpr != null);
                            retHoleHashMap.put(methodKeyExpr, greenExpr);
                        }
                        break;
                    case NEGCONDITION:
                        if(isMethodSummary) {
                            System.out.println("unsupported negCondition hole in method summary");
                            return true;
                        } else {
                            assert (instructionInfo != null);
                            greenExpr = instructionInfo.getNegCondition();
                            assert (greenExpr != null);
                            retHoleHashMap.put(methodKeyExpr, greenExpr);
                        }
                        break;
                    case LOCAL_OUTPUT:
                    case INTERMEDIATE:
                        spfExpr = makeSymbolicInteger(methodKeyHole.getHoleVarName() + pathLabelCount);
                        greenExpr = SPFToGreenExpr(spfExpr);
                        retHoleHashMap.put(methodKeyHole, greenExpr);
                        break;
                    case FIELD_OUTPUT:
                        if(isMethodSummary) {
                            HoleExpression.FieldInfo methodKeyHoleFieldInfo = methodKeyHole.getFieldInfo();
                            if (!methodKeyHoleFieldInfo.isStaticField) {
                                if (methodKeyHoleFieldInfo.localStackSlot == 0) {
                                    assert (callSiteInfo.paramList.size() > 0);
                                    methodKeyHoleFieldInfo.callSiteStackSlot = ((HoleExpression) callSiteInfo.paramList.get(0)).getLocalStackSlot();
                                    methodKeyHole.setFieldInfo(methodKeyHoleFieldInfo.className, methodKeyHoleFieldInfo.fieldName,
                                            methodKeyHoleFieldInfo.methodName,
                                            methodKeyHoleFieldInfo.localStackSlot, methodKeyHoleFieldInfo.callSiteStackSlot, methodKeyHoleFieldInfo.writeValue,
                                            methodKeyHoleFieldInfo.isStaticField, methodKeyHoleFieldInfo.useHole);
                                } else return true;
                            }
                            //populateOutputs does not use the value mapped to methodKeyHole for FIELD_OUTPUT holes
                        }
                        retHoleHashMap.put(methodKeyHole, null);
                        break;
                    case NONE:
                        System.out.println("expression marked as hole with NONE hole type: " +
                                methodKeyHole.toString());
                        assert (false);
                        break;
                    case INVOKE:
                    case FIELD_INPUT:
                    case LOCAL_INPUT:
                    default:
                        break;
                }
            }
            return false;
        }
    }

    private class FillInputHoles {
        private final boolean isMethodSummary;
        private boolean failure;
        private final StackFrame stackFrame;
        private final ThreadInfo ti;
        private LinkedHashMap<Expression, Expression> retHoleHashMap;
        private InvokeInfo callSiteInfo;
        private LinkedHashMap<Expression, Expression> methodHoles;
        private ArrayList<Expression> paramEqList;

        public FillInputHoles(StackFrame stackFrame, ThreadInfo ti, LinkedHashMap<Expression, Expression> retHoleHashMap,
                              InvokeInfo callSiteInfo, LinkedHashMap<Expression, Expression> methodHoles,
                              boolean isMethodSummary) {
            this.stackFrame = stackFrame;
            this.ti = ti;
            this.retHoleHashMap = retHoleHashMap;
            this.callSiteInfo = callSiteInfo;
            this.methodHoles = methodHoles;
            this.isMethodSummary = isMethodSummary;
        }

        boolean failure() {
            return failure;
        }

        public ArrayList<Expression> getParamEqList() {
            return paramEqList;
        }

        public FillInputHoles invoke() {
            gov.nasa.jpf.symbc.numeric.Expression spfExpr;
            Expression greenExpr;
            paramEqList = new ArrayList<>();
            for(Map.Entry<Expression, Expression> entry1 : methodHoles.entrySet()) {
                Expression methodKeyExpr = entry1.getKey();
                assert(methodKeyExpr instanceof HoleExpression);
                HoleExpression methodKeyHole = (HoleExpression) methodKeyExpr;
                assert(methodKeyHole.isHole());
                switch(methodKeyHole.getHoleType()) {
                    //LOCAL_INPUTs can be mapped to parameters at the call site, non-parameter local inputs
                    // need to be mapped to intermediate variables since we cannot create a stack for the summarized method
                    case LOCAL_INPUT:
                        //get the latest value written into this local, not the value in the local at the beginning of
                        //this region
                        if(methodKeyHole.dependsOn != null) {
                            HoleExpression holeExpression = (HoleExpression) methodKeyHole.dependsOn;
                            assert(holeExpression.getHoleType() == HoleExpression.HoleType.LOCAL_OUTPUT);
                            assert(holeExpression.isLatestWrite);
                            assert(retHoleHashMap.containsKey(holeExpression));
                            retHoleHashMap.put(methodKeyHole, retHoleHashMap.get(holeExpression));
                        } else {
                            if(isMethodSummary) {
                                //local inputs used in method summary have to come from the filled-up holes in paramList
                                if (methodKeyHole.getLocalStackSlot() < callSiteInfo.paramList.size()) {
                                    int methodLocalStackSlot = methodKeyHole.getLocalStackSlot();
                                    if (callSiteInfo.paramList.get(methodLocalStackSlot) instanceof HoleExpression) {
                                        //int callSiteLocalStackSlot = ((HoleExpression)callSiteInfo.paramList.get(methodLocalStackSlot)).getLocalStackSlot();
                                        //methodKeyHole.setLocalStackSlot(callSiteLocalStackSlot);
                                        retHoleHashMap.put(methodKeyHole, retHoleHashMap.get(callSiteInfo.paramList.get(methodLocalStackSlot)));
                                    }
                                    else //a constant could have been passed as an argument instead of a variable
                                        retHoleHashMap.put(methodKeyHole, callSiteInfo.paramList.get(methodLocalStackSlot));
                                    paramEqList.add(new Operation(Operation.Operator.EQ,
                                            methodKeyHole,
                                            callSiteInfo.paramList.get(methodLocalStackSlot)));
                                } else {
                                    //Local variables in the method summary should just become intermediate variables
                                    gov.nasa.jpf.symbc.numeric.Expression finalValueSPF =
                                            makeSymbolicInteger(methodKeyHole.getHoleVarName() + pathLabelCount);
                                    Expression finalValueGreen = SPFToGreenExpr(finalValueSPF);
                                    retHoleHashMap.put(methodKeyHole, finalValueGreen);
                                }
                            } else {
                                gov.nasa.jpf.symbc.numeric.Expression finalValueSPF =
                                        (gov.nasa.jpf.symbc.numeric.Expression) stackFrame.getLocalAttr(methodKeyHole.getLocalStackSlot());
                                if (finalValueSPF == null)
                                    finalValueSPF = new IntegerConstant(stackFrame.getLocalVariable(methodKeyHole.getLocalStackSlot()));
                                Expression finalValueGreen = SPFToGreenExpr(finalValueSPF);
                                retHoleHashMap.put(methodKeyHole, finalValueGreen);
                            }
                        }
                        break;
                    case FIELD_INPUT:
                        if(methodKeyHole.dependsOn != null) {
                            //get the latest value written into this field, not the value in the field at the beginning of
                            //this region
                            HoleExpression holeExpression = (HoleExpression) methodKeyHole.dependsOn;
                            assert(holeExpression.getHoleType() == HoleExpression.HoleType.FIELD_OUTPUT);
                            assert(holeExpression.isLatestWrite);
                            assert(retHoleHashMap.containsKey(holeExpression.getFieldInfo().writeValue));
                            retHoleHashMap.put(methodKeyHole, retHoleHashMap.get(holeExpression.getFieldInfo().writeValue));
                        } else {
                            HoleExpression.FieldInfo methodKeyHoleFieldInfo = methodKeyHole.getFieldInfo();
                            assert (methodKeyHoleFieldInfo != null);
                            if(isMethodSummary) {
                                if (!methodKeyHoleFieldInfo.isStaticField) {
                                    if (methodKeyHoleFieldInfo.localStackSlot == 0) {
                                        assert (callSiteInfo.paramList.size() > 0);
                                        assert(HoleExpression.isLocal(callSiteInfo.paramList.get(0)));
                                        int callSiteStackSlot = ((HoleExpression)
                                                callSiteInfo.paramList.get(0)).getGlobalOrLocalStackSlot(ti.getTopFrame().getClassInfo().getName(),
                                                ti.getTopFrame().getMethodInfo().getName());
                                        methodKeyHoleFieldInfo.callSiteStackSlot = callSiteStackSlot;
                                    } else {
                                        // method summary uses a field from an object that failure a local inside the method
                                        // this cannot be handled during veritesting because we cannot create an object
                                        // when using a method summary
                                        failure = true;
                                        return this;
                                    }
                                }
                            }
                            spfExpr = fillFieldHole(ti, stackFrame, methodKeyHoleFieldInfo, retHoleHashMap, true, null);
                            if (spfExpr == null) {
                                failure = true;
                                return this;
                            }
                            greenExpr = SPFToGreenExpr(spfExpr);
                            retHoleHashMap.put(methodKeyHole, greenExpr);
                        }
                        break;
                    case INVOKE:
                        if(isMethodSummary) {
                            //Update the global stack slot of holes used in the invoke-call of method summary
                            // based on the caller's paramList for all local holes
                            InvokeInfo methodCallSiteInfo = methodKeyHole.getInvokeInfo();
                            for(int i=0; i<methodCallSiteInfo.paramList.size(); i++) {
                                if(HoleExpression.isLocal(methodCallSiteInfo.paramList.get(i))) {
                                    assert(methodCallSiteInfo.paramList.get(i) instanceof HoleExpression);
                                    HoleExpression h = (HoleExpression) methodCallSiteInfo.paramList.get(i);
                                    int methodCallSiteStackSlot = h.getLocalStackSlot();
                                    if(methodCallSiteStackSlot < callSiteInfo.paramList.size()) {
                                        if(HoleExpression.isLocal(callSiteInfo.paramList.get(methodCallSiteStackSlot))) {
                                            assert(callSiteInfo.paramList.get(methodCallSiteStackSlot) instanceof HoleExpression);
                                            HoleExpression callSiteHole = (HoleExpression) callSiteInfo.paramList.get(methodCallSiteStackSlot);
                                            //It is important to use getGlobalOrLocalStackSlot here, not getLocalStackSlot
                                            // because we would like the caller's globalStackSlot to be used if possible
                                            h.setGlobalStackSlot(callSiteHole.getGlobalOrLocalStackSlot(ti.getTopFrame().getClassInfo().getName(),
                                                    ti.getTopFrame().getMethodInfo().getName()));
                                            methodCallSiteInfo.paramList.set(i, h);
                                        }
                                        else {
                                            Expression callSiteExpression = callSiteInfo.paramList.get(methodCallSiteStackSlot);
                                            methodCallSiteInfo.paramList.set(i, callSiteExpression);
                                            if(callSiteExpression instanceof HoleExpression) {
                                                if (methodHoles.containsKey(callSiteInfo.paramList.get(methodCallSiteStackSlot)) == false)
                                                    methodHoles.put(callSiteExpression, callSiteExpression);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        break;
                    default: break;
                }
            }
            failure = false;
            return this;
        }
    }

    private class FillMethodSummary {
        private boolean myResult;
        private StackFrame stackFrame;
        private ThreadInfo ti;
        private LinkedHashMap<Expression, Expression> holeHashMap;
        private LinkedHashMap<Expression, Expression> retHoleHashMap;
        private Expression additionalAST;
        private HoleExpression keyHoleExpression;
        private InvokeInfo callSiteInfo;
        private VeritestingRegion methodSummary;

        public FillMethodSummary(StackFrame stackFrame, ThreadInfo ti, LinkedHashMap<Expression, Expression> holeHashMap,
                                 LinkedHashMap<Expression, Expression> retHoleHashMap, Expression additionalAST,
                                 HoleExpression keyHoleExpression, InvokeInfo callSiteInfo, VeritestingRegion methodSummary) {
            this.stackFrame = stackFrame;
            this.ti = ti;
            this.holeHashMap = holeHashMap;
            this.retHoleHashMap = retHoleHashMap;
            this.additionalAST = additionalAST;
            this.keyHoleExpression = keyHoleExpression;
            this.callSiteInfo = callSiteInfo;
            this.methodSummary = methodSummary;
        }

        boolean is() {
            return myResult;
        }

        public LinkedHashMap<Expression, Expression> getRetHoleHashMap() {
            return retHoleHashMap;
        }

        public Expression getAdditionalAST() {
            return additionalAST;
        }

        public FillMethodSummary invoke() {
            FillNonInputHoles fillNonInputHoles;
            LinkedHashMap<Expression, Expression> methodHoles = methodSummary.getHoleHashMap();
            if(hasRWInterference(holeHashMap, methodHoles, callSiteInfo, stackFrame)) {
                methodSummaryRWInterference++;
                System.out.println("method summary hole interferes with outer region");
                myResult = true;
                return this;
            }
            fillNonInputHoles =
                    new FillNonInputHoles(retHoleHashMap, callSiteInfo, methodHoles, null, true);
            if (fillNonInputHoles.invoke()) {
                myResult = true;
                return this;
            }
            retHoleHashMap = fillNonInputHoles.retHoleHashMap;

            FillInputHoles fillInputHolesMS =
                    new FillInputHoles(stackFrame, ti, retHoleHashMap, callSiteInfo, methodHoles, true).invoke();
            if (fillInputHolesMS.failure()) {
                myResult = true;
                return this;
            }
            ArrayList<Expression> paramEqList = fillInputHolesMS.getParamEqList();
            retHoleHashMap = fillInputHolesMS.retHoleHashMap;

            FillInvokeHole fillInvokeHole = new FillInvokeHole(stackFrame, ti, methodHoles, retHoleHashMap, additionalAST).invoke();
            if (fillInvokeHole.is()) {
                myResult = true;
                return this;
            }
            retHoleHashMap = fillInvokeHole.getRetHoleHashMap();
            additionalAST = fillInvokeHole.getAdditionalAST();

            Expression retValEq = null;
            if (methodSummary.retVal != null)
                retValEq = new Operation(Operation.Operator.EQ, methodSummary.retVal, keyHoleExpression);
            Expression mappingOperation = retValEq;
            for(int i=0; i < paramEqList.size(); i++) {
                //paramList.length-1 because there won't be a constraint created for the object reference
                if(mappingOperation != null)
                    mappingOperation = new Operation(Operation.Operator.AND, mappingOperation, paramEqList.get(i));
                else mappingOperation = paramEqList.get(i);
            }
            if (methodSummary.getSummaryExpression() != null)
                mappingOperation = new Operation(Operation.Operator.AND, mappingOperation, methodSummary.getSummaryExpression());
            if (additionalAST != null)
                additionalAST = new Operation(Operation.Operator.AND, additionalAST, mappingOperation);
            else additionalAST = mappingOperation;
            Expression finalValueGreen = SPFToGreenExpr(makeSymbolicInteger(keyHoleExpression.getHoleVarName() + pathLabelCount));
            retHoleHashMap.put(keyHoleExpression, finalValueGreen);
            methodSummary.ranIntoCount++;
            methodSummary.usedCount++;
            myResult = false;
            return this;
        }
    }

    private class FillInvokeHole {
        private boolean myResult;
        private StackFrame stackFrame;
        private ThreadInfo ti;
        private LinkedHashMap<Expression, Expression> holeHashMap;
        private LinkedHashMap<Expression, Expression> retHoleHashMap;
        private Expression additionalAST;

        public FillInvokeHole(StackFrame stackFrame, ThreadInfo ti, LinkedHashMap<Expression, Expression> holeHashMap,
                              LinkedHashMap<Expression, Expression> retHoleHashMap, Expression additionalAST) {
            this.stackFrame = stackFrame;
            this.ti = ti;
            this.holeHashMap = holeHashMap;
            this.retHoleHashMap = retHoleHashMap;
            this.additionalAST = additionalAST;
        }

        boolean is() {
            return myResult;
        }

        public LinkedHashMap<Expression, Expression> getRetHoleHashMap() {
            return retHoleHashMap;
        }

        public Expression getAdditionalAST() {
            return additionalAST;
        }

        public FillInvokeHole invoke() {
            // resolve all invoke holes in the current region's summary expression
            for(Map.Entry<Expression, Expression> entry : holeHashMap.entrySet()) {
                Expression key = entry.getKey();
                assert (key instanceof HoleExpression);
                HoleExpression keyHoleExpression = (HoleExpression) key;
                assert (keyHoleExpression.isHole());
                switch (keyHoleExpression.getHoleType()) {
                    case INVOKE:
                        InvokeInfo callSiteInfo = keyHoleExpression.getInvokeInfo();
                        ClassInfo ci = null;
                        if (callSiteInfo.isVirtualInvoke) {
                            Expression callingObject = retHoleHashMap.get(callSiteInfo.paramList.get(0));
                            ci = ti.getClassInfo(((IntConstant) callingObject).getValue());
                        }
                        if (callSiteInfo.isStaticInvoke) {
                            ci = ClassLoaderInfo.getCurrentResolvedClassInfo(callSiteInfo.className);
                        }

                        // if ci failure null, that means either MyIVisitor.visitInvoke has a bug or we failed to load the class
                        assert(ci != null);
                        //Change the class name based on the call site object reference
                        callSiteInfo.className = ci.getName();
                        //If there exists a invokeVirtual for a method that we weren't able to summarize, skip veritesting
                        String key1 = callSiteInfo.className + "." + callSiteInfo.methodName + callSiteInfo.methodSignature + "#0";
                        FNV1 fnv = new FNV1a64();
                        fnv.init(key1);
                        long hash = fnv.getHash();
                        if(!veritestingRegions.containsKey(key1)) {
                            System.out.println("Could not find method summary for " +
                                    callSiteInfo.className+"."+callSiteInfo.methodName+"#0");
                            myResult = true;
                            return this;
                        }
                        //All holes in callSiteInfo.paramList will also be present in holeHashmap and will be filled up here
                        for (Expression h : callSiteInfo.paramList) {
                            if (h instanceof HoleExpression) {
                                if (holeHashMap.containsKey(h) == false) {
                                    System.out.println("invokeHole's holeHashmap does not contain hole: " + h.toString());
                                    assert(false);
                                }
                            }
                        }
                        VeritestingRegion methodSummary = veritestingRegions.get(key1);
                        FillMethodSummary fillMethodSummary = new FillMethodSummary(stackFrame, ti, holeHashMap,
                                retHoleHashMap, additionalAST, keyHoleExpression, callSiteInfo, methodSummary).invoke();
                        if (fillMethodSummary.is()) {
                            myResult = true;
                            return this;
                        }
                        retHoleHashMap = fillMethodSummary.getRetHoleHashMap();
                        additionalAST = fillMethodSummary.getAdditionalAST();
                        break;
                }
            }
            myResult = false;
            return this;
        }
    }

  /*public IntegerExpression constantFold(IntegerExpression integerExpression) {
    if(integerExpression instanceof IntegerConstant) return integerExpression;
    if(integerExpression instanceof ComplexNonLinearIntegerExpression) {
      ComplexNonLinearIntegerExpression cnlie = (ComplexNonLinearIntegerExpression) integerExpression;
      if (cnlie.getLeft() instanceof IntegerConstant && cnlie.getRight() instanceof IntegerConstant) {
        int left = ((IntegerConstant) cnlie.getLeft()).value();
        int right = ((IntegerConstant) cnlie.getRight()).value();
        int failure = 0;
        switch (cnlie.getOperator()) {
          case DIV:
            failure = left / right;
            break;
          case MUL:
            failure = left * right;
            break;
          case MINUS:
            failure = left - right;
            break;
          case PLUS:
            failure = left + right;
            break;
          case CMP:
            failure = Integer.compare(left, right);
            break;
          case AND:
            failure = left & right;
            break;
          case OR:
            failure = left | right;
            break;
          case XOR:
            failure = left ^ right;
            break;
          case SHIFTL:
            failure = left << right;
            break;
          case SHIFTR:
            failure = left >> right;
            break;
          case SHIFTUR:
            failure = left >>> right;
            break;
          case REM:
            failure = left % right;
            break;
          case NONE_OP:
            switch (cnlie.getComparator()) {
              case EQ:
                failure = (left == right) ? 1 : 0;
                break;
              case NE:
                failure = (left != right) ? 1 : 0;
                break;
              case LT:
                failure = (left < right) ? 1 : 0;
                break;
              case LE:
                failure = (left <= right) ? 1 : 0;
                break;
              case GT:
                failure = (left > right) ? 1 : 0;
                break;
              case GE:
                failure = (left >= right) ? 1 : 0;
                break;
              case LOGICAL_AND:
                failure = ((left != 0) && (right != 0)) ? 1 : 0;
                break;
              case LOGICAL_OR:
                failure = ((left != 0) || (right != 0)) ? 1 : 0;
                break;
              case NONE_CMP:
                System.out.println("constantFold found NONE_OP and NONE_CMP");
                assert(false);
                break;
              default:
                System.out.println("constantFold found NONE_OP and undefined comparator (" + cnlie.getComparator() + ")");
                assert(false);
                break;
            }
            break;
          default:
            System.out.println("constantFold found undefined operator (" + cnlie.getOperator() + ")");
            assert (false);
        }
        return new IntegerConstant(failure);
      }
      cnlie.setLeft(constantFold(cnlie.getLeft()));
      cnlie.setRight(constantFold(cnlie.getRight()));
      if(cnlie.getLeft() instanceof IntegerConstant) {
        if(cnlie.getRight() instanceof IntegerConstant) {
          if(cnlie.getOperator() == NONE_OP) {
            return constantFold(new ComplexNonLinearIntegerExpression(cnlie.getLeft(), cnlie.getComparator(), cnlie.getRight()));
          }
          if(cnlie.getComparator() == NONE_CMP) {
            return constantFold(new ComplexNonLinearIntegerExpression(cnlie.getLeft(), cnlie.getOperator(), cnlie.getRight()));
          }
        }
      }
    }
    return integerExpression;
}*/

}
