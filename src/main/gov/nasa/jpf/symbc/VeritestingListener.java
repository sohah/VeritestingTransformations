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


import gov.nasa.jpf.Config;
import gov.nasa.jpf.JPF;
import gov.nasa.jpf.PropertyListenerAdapter;
import gov.nasa.jpf.jvm.JVMDirectCallStackFrame;
import gov.nasa.jpf.jvm.bytecode.GOTO;
import gov.nasa.jpf.report.ConsolePublisher;
import gov.nasa.jpf.report.Publisher;
import gov.nasa.jpf.report.PublisherExtension;
import gov.nasa.jpf.symbc.numeric.*;
import gov.nasa.jpf.symbc.veritesting.*;
import gov.nasa.jpf.symbc.veritesting.ChoiceGenerator.StaticBranchChoiceGenerator;
import gov.nasa.jpf.symbc.veritesting.ChoiceGenerator.StaticPCChoiceGenerator;
import gov.nasa.jpf.symbc.veritesting.ChoiceGenerator.StaticSummaryChoiceGenerator;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.FailEntry;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.SpfUtil;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.StatisticManager;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.AstToGreen.AstToGreenVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.FieldRefTypeTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicOutputTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.SlotParamTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.SPFCases.SpfCasesPass1Visitor;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.SPFCases.SpfCasesPass2Visitor;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.SPFCases.SpfToGreenVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Uniquness.UniqueRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.arrayaccess.ArraySSAVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.fieldaccess.FieldSSAVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.fieldaccess.SubscriptPair;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.fieldaccess.SubstituteGetOutput;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.linearization.LinearizationTransformation;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.CreateStaticRegions;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution.SubstitutionVisitor;

import gov.nasa.jpf.symbc.veritesting.ast.transformations.typepropagation.TypePropagationVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.PrettyPrintVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.StmtPrintVisitor;
import gov.nasa.jpf.vm.*;
import gov.nasa.jpf.vm.Instruction;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.VisitorException;

import java.io.PrintWriter;
import java.util.*;
import java.util.concurrent.TimeUnit;

import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.createGreenVar;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.greenToSPFExpression;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.isPCSat;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.SpfUtil.isUnsupportedRegionEnd;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.StatisticManager.hgOrdRegionInstance;
import static gov.nasa.jpf.symbc.veritesting.ast.transformations.arrayaccess.ArraySSAVisitor.doArrayStore;

public class VeritestingListener extends PropertyListenerAdapter implements PublisherExtension {


    //TODO: make these into configuration options
    public static int veritestingMode = 0;

    public static long totalSolverTime = 0, z3Time = 0;
    public static long parseTime = 0;
    public static long solverAllocTime = 0;
    public static long cleanupTime = 0;
    public static int solverCount = 0;
    public static final int maxStaticExplorationDepth = 2;
    public static boolean initializeTime = true;
    public static int veritestRegionCount = 0;
    private static long staticAnalysisDur;
    private final long runStartTime = System.nanoTime();
    public static StatisticManager statisticManager = new StatisticManager();
    private static int veritestRegionExpectedCount = -1;

    public enum VeritestingMode { VANILLASPF, VERITESTING, HIGHORDER, SPFCASES }

    private static VeritestingMode runMode;
    public static boolean performanceMode = false;

    public VeritestingListener(Config conf, JPF jpf) {
        if (conf.hasValue("veritestingMode")) {
            veritestingMode = conf.getInt("veritestingMode");
            runMode = veritestingMode == 4 ? VeritestingMode.SPFCASES :
                    ((veritestingMode == 3 ? VeritestingMode.HIGHORDER :
                            (veritestingMode == 2 ? VeritestingMode.VERITESTING : VeritestingMode.VANILLASPF)));

            switch (runMode) {
                case VANILLASPF:
                    System.out.println("* Warning: either invalid or no veritestingMode specified.");
                    System.out.println("* Warning: set veritestingMode to 1 to use vanilla SPF with VeritestingListener");
                    System.out.println("* Warning: set veritestingMode to 2 to use veritesting");
                    System.out.println("* Warning: set veritestingMode to 3 to use veritesting with higher order regions");
                    System.out.println("* Warning: set veritestingMode to 4 to use veritesting with higher order regions and SPFCases");
                    System.out.println("* Warning: resetting veritestingMode to 0 (aka use vanilla SPF)");
                    veritestingMode = 0;
                    break;
                case VERITESTING:
                    System.out.println("* running veritesting without SPFCases.");
                    break;
                case SPFCASES:
                    System.out.println("* running veritesting with SPFCases.");
                    break;
            }

            if (conf.hasValue("performanceMode"))
                performanceMode = conf.getBoolean("performanceMode");

            if (conf.hasValue("veritestRegionExpectedCount"))
                veritestRegionExpectedCount = conf.getInt("veritestRegionExpectedCount");

            StatisticManager.veritestingRunning = true;
            jpf.addPublisherExtension(ConsolePublisher.class, this);
        }
    }

    public SymbolicInteger makeSymbolicInteger(String name) {
        //return new SymbolicInteger(name, MinMax.getVarMinInt(name), MinMax.getVarMaxInt(name));
        return new SymbolicInteger(name, Integer.MIN_VALUE, Integer.MAX_VALUE);
    }

    /**
     * Listener's main method that checks every instruction for being a potential veritesting region.
     *
     * @param vm                   Virtual Machine.
     * @param ti                   Current running Thread.
     * @param instructionToExecute instruction to be executed.
     */
    public void executeInstruction(VM vm, ThreadInfo ti, Instruction instructionToExecute) {
        if (runMode == VeritestingMode.VANILLASPF) return;
        boolean noVeritestingFlag = false;
        StackFrame curr = ti.getTopFrame();
        // Begin equivalence checking code
        while (!JVMDirectCallStackFrame.class.isInstance(curr)) {
            if (curr.getMethodInfo().getName().equals("NoVeritest")) {
                noVeritestingFlag = true;
                break;
            } else curr = curr.getPrevious();
        }
        if (noVeritestingFlag)
            return;
        // End equivalence checking code

        MethodInfo methodInfo = instructionToExecute.getMethodInfo();
        String className = methodInfo.getClassName();
        String methodName = methodInfo.getName();
        String methodSignature = methodInfo.getSignature();
        int offset = instructionToExecute.getPosition();
        String key = CreateStaticRegions.constructRegionIdentifier(className + "." + methodName + methodSignature, offset);

        StatisticManager.instructionToExec = key;

        if (initializeTime) {
            discoverRegions(ti); // static analysis to discover regions
            initializeTime = false;
        } else {
            try {
                HashMap<String, StaticRegion> regionsMap = VeritestingMain.veriRegions;
                StaticRegion staticRegion = regionsMap.get(key);
                if ((staticRegion != null) && !(staticRegion.isMethodRegion)) {
                    //if (SpfUtil.isSymCond(staticRegion.staticStmt)) {
                    if (SpfUtil.isSymCond(ti.getTopFrame(), staticRegion.staticStmt, (SlotParamTable) staticRegion.slotParamTable, instructionToExecute)) {
                        if (runMode != VeritestingMode.SPFCASES) {
                            // If region ends on a stack operand consuming instruction that isn't a store, then abort the region
                            Instruction regionEndInsn = isUnsupportedRegionEnd(staticRegion, instructionToExecute);
                            if (regionEndInsn != null) {
                                throw new StaticRegionException("Unsupported region end instruction: " + regionEndInsn);
                            }
                            DynamicRegion dynRegion = runVeritesting(ti, instructionToExecute, staticRegion, key);
                            Instruction nextInstruction = setupSPF(ti, instructionToExecute, dynRegion);
                            ++veritestRegionCount;
                            ti.setNextPC(nextInstruction);
                            statisticManager.updateVeriSuccForRegion(key);

                            System.out.println("------------- Region was successfully veritested --------------- ");
                        } else {
                            runVeritestingWithSPF(ti, vm, instructionToExecute, staticRegion, key);
                        }
                    } else
                        statisticManager.updateConcreteHitStatForRegion(key);
                }
            } catch (IllegalArgumentException e) {
                statisticManager.updateSPFHitForRegion(key, e.getMessage());
                System.out.println("!!!!!!!! Aborting Veritesting !!!!!!!!!!!! " + "\n" + e.getMessage() + "\n");
                return;
            } catch (StaticRegionException sre) {
                statisticManager.updateSPFHitForRegion(key, sre.getMessage());
                System.out.println("!!!!!!!! Aborting Veritesting !!!!!!!!!!!! " + "\n" + sre.getMessage() + "\n");
                return;
            }
            catch (VisitorException greenEx) {
                statisticManager.updateSPFHitForRegion(key, greenEx.getMessage());
                System.out.println("!!!!!!!! Aborting Veritesting !!!!!!!!!!!! " + "\n" + greenEx.getMessage() + "\n");
                return;
            } catch (CloneNotSupportedException e) {
                System.out.println("!!!!!!!! Aborting Veritesting !!!!!!!!!!!! " + "\n" + e.getMessage() + "\n");
                e.printStackTrace();
                return;
            }
        }
    }

    private void runVeritestingWithSPF(ThreadInfo ti, VM vm, Instruction instructionToExecute, StaticRegion staticRegion, String key) throws StaticRegionException, CloneNotSupportedException, VisitorException {
        if (!ti.isFirstStepInsn()) { // first time around
            StaticPCChoiceGenerator newCG;
            DynamicRegion dynRegion = runVeritesting(ti, instructionToExecute, staticRegion, key);
            dynRegion = greenTranformationForSPFCases(dynRegion);
            if (StaticPCChoiceGenerator.getKind(instructionToExecute) == StaticPCChoiceGenerator.Kind.OTHER) {
                newCG = new StaticSummaryChoiceGenerator(dynRegion, instructionToExecute);
            } else {
                newCG = new StaticBranchChoiceGenerator(dynRegion, instructionToExecute);
            }
            newCG.makeVeritestingCG(ti);

            SystemState systemState = vm.getSystemState();
            systemState.setNextChoiceGenerator(newCG);
            ti.setNextPC(instructionToExecute);
        } else {
            ChoiceGenerator<?> cg = ti.getVM().getSystemState().getChoiceGenerator();
            if (cg instanceof StaticPCChoiceGenerator) {
                StaticPCChoiceGenerator vcg = (StaticPCChoiceGenerator) cg;
                int choice = (Integer) cg.getNextChoice();
                Instruction nextInstruction = null;
                try {
                    nextInstruction = vcg.execute(ti, instructionToExecute, choice);
                } catch (StaticRegionException sre) {
                    System.out.println(sre.toString());
                    return;
                }

                ti.setNextPC(nextInstruction);
            }
        }
    }

    /**
     * creates a green expression for all SPFCases of the region.
     *
     * @param dynRegion Dynamic Region where SPFCases needs to be transformed into a green expression
     * @return A new dynamic region that has SPFCaseList changed to greenExpressions. It will also have greenSPFRegionSummary populated with the SPF appropriate predicate.
     */
    private DynamicRegion greenTranformationForSPFCases(DynamicRegion dynRegion) {
        return SpfToGreenVisitor.execute(dynRegion);
    }


    private DynamicRegion runVeritesting(ThreadInfo ti, Instruction instructionToExecute, StaticRegion staticRegion, String key) throws CloneNotSupportedException, StaticRegionException, VisitorException {
        System.out.println("\n---------- STARTING Transformations for conditional region: " + key +
                "\n" + PrettyPrintVisitor.print(staticRegion.staticStmt) + "\n");
        staticRegion.slotParamTable.print();
        staticRegion.inputTable.print();
        staticRegion.outputTable.print();
        staticRegion.varTypeTable.print();
        /*-------------- UNIQUENESS TRANSFORMATION ---------------*/
        DynamicRegion dynRegion = UniqueRegion.execute(staticRegion);

        /*--------------- SUBSTITUTION TRANSFORMATION ---------------*/
        dynRegion = SubstitutionVisitor.execute(ti, dynRegion);

        System.out.println("\n--------------- FIELD REFERENCE TRANSFORMATION ---------------\n");
        dynRegion = FieldSSAVisitor.execute(ti, dynRegion);
        TypePropagationVisitor.propagateTypes(dynRegion);

        System.out.println("\n--------------- ARRAY TRANSFORMATION ---------------\n");
        dynRegion = ArraySSAVisitor.execute(ti, dynRegion);
        System.out.println(StmtPrintVisitor.print(dynRegion.dynStmt));
        dynRegion = UniqueRegion.execute(dynRegion);

        if(runMode == VeritestingMode.SPFCASES) {
        /*-------------- SPFCases TRANSFORMATION 1ST PASS ---------------*/
            dynRegion = SpfCasesPass1Visitor.execute(ti, dynRegion, null);

        /*-------------- SPFCases TRANSFORMATION 1ST PASS ---------------*/
            dynRegion = SpfCasesPass2Visitor.execute(dynRegion);
        }
        /*--------------- LINEARIZATION TRANSFORMATION ---------------*/
        LinearizationTransformation linearTrans = new LinearizationTransformation();
        dynRegion = linearTrans.execute(dynRegion);


        /*--------------- TO GREEN TRANSFORMATION ---------------*/
        dynRegion = AstToGreenVisitor.execute(dynRegion);

        return dynRegion;
    }

    /**
     * This populates the Output of the summarized region to SPF.
     *
     * @param ti        Currently running thread.
     * @param ins       Branch instruction that indicates beginning of the region.
     * @param dynRegion Dynamic region that has been summarized.
     * @throws StaticRegionException Exception to indicate a problem while setting SPF.
     */

    public static Instruction setupSPF(ThreadInfo ti, Instruction ins, DynamicRegion dynRegion) throws StaticRegionException {
        if (canSetPC(ti, dynRegion.regionSummary)) {
            populateSlots(ti, dynRegion);
            populateFieldOutputs(ti, dynRegion);
            populateArrayOutputs(ti, dynRegion);
            clearStack(ti.getModifiableTopFrame(), ins);
            return advanceSpf(ti, ins, dynRegion);
        }
        return null;
    }

    /**
     * This method checks that the current PathCondition and after appending the summarized region is satisfiable.
     *
     * @param ti            Currently running thread.
     * @param regionSummary Finaly summary of the region, after all transformations has been successfully completed.
     * @return PathCondition is still satisfiable or not.
     * @throws StaticRegionException Exception to indicate a problem while checking SAT of the updated PathCondition.
     */
    private static boolean canSetPC(ThreadInfo ti, Expression regionSummary) throws StaticRegionException {
        PathCondition pc;


        if (ti.getVM().getSystemState().getChoiceGenerator() instanceof PCChoiceGenerator) {
            pc = ((PCChoiceGenerator) (ti.getVM().getSystemState().getChoiceGenerator())).getCurrentPC();
        }
        else {
            pc = new PathCondition();
            pc._addDet(new GreenConstraint(Operation.TRUE));
        }
        pc._addDet(new GreenConstraint(regionSummary));
        // if we're trying to run fast, then assume that the region summary is satisfiable in any non-SPFCASES mode
        if ((performanceMode && (runMode == VeritestingMode.VERITESTING || runMode == VeritestingMode.HIGHORDER)) ||
                isPCSat(pc)) {
            ((PCChoiceGenerator) ti.getVM().getSystemState().getChoiceGenerator()).setCurrentPC(pc);
            return true;
        } else {
            if (runMode == VeritestingMode.SPFCASES)
                ti.getVM().getSystemState().setIgnored(true); //to ignore counting of the current choice generator.
            throw new StaticRegionException("Path condition is unsat, no region is created.");
        }
    }

    /**
     * This pop up operands of the if instruction that begins the region.
     *
     * @param sf  Current StackFrame.
     * @param ins Current executing instruction
     * @throws StaticRegionException Exception to indicate a problem while clearning the stack.
     */

    private static void clearStack(StackFrame sf, Instruction ins) throws StaticRegionException {
        int numOperands = SpfUtil.getOperandNumber(ins.getMnemonic());
        while (numOperands > 0) {
            sf.pop();
            numOperands--;
        }
    }


    //TODO: I need to use the wala name not number here.

    /**
     * Populates SPF stack slot with the output of the veritesting region.
     *
     * @param ti        Current executing thread.
     * @param dynRegion Dynamic region that has been successfully transformed and summarized.
     */
    private static void populateSlots(ThreadInfo ti, DynamicRegion dynRegion) {
        StackFrame sf = ti.getTopFrame();
        DynamicOutputTable dynOutputTable = dynRegion.outputTable;
        List<Integer> slots = dynOutputTable.getKeys();

        Iterator slotItr = slots.iterator();

        while (slotItr.hasNext()) {
            Integer slot = (Integer) slotItr.next();
            Variable var = dynOutputTable.lookup(slot);
            assert(var instanceof WalaVarExpr);
            Expression symVar = createGreenVar((String) dynRegion.varTypeTable.lookup(var), ((WalaVarExpr) var).getSymName());
            sf.setSlotAttr(slot, greenToSPFExpression(symVar));
        }
    }

    private static void populateFieldOutputs(ThreadInfo ti, DynamicRegion dynRegion) throws StaticRegionException {
        Iterator itr = dynRegion.psm.getUniqueFieldAccess().iterator();
        while (itr.hasNext()) {
            FieldRefVarExpr expr = (FieldRefVarExpr) itr.next();
            Expression symVar = createGreenVar(dynRegion.fieldRefTypeTable.lookup(expr), expr.getSymName());
            new SubstituteGetOutput(ti, expr.fieldRef, false, greenToSPFExpression(symVar)).invoke();
        }
    }

    private static void populateArrayOutputs(ThreadInfo ti, DynamicRegion dynRegion) throws StaticRegionException {
        Iterator itr = dynRegion.arrayPSM.getUniqueArrayAccess().iterator();
        while (itr.hasNext()) {
            ArrayRefVarExpr expr = (ArrayRefVarExpr) itr.next();
            Expression symVar = createGreenVar(dynRegion.fieldRefTypeTable.lookup(expr), expr.getSymName());
            doArrayStore(ti, expr, symVar, dynRegion.fieldRefTypeTable.lookup(expr));
        }
    }

    /**
     * Steps SPF to the end of the region.
     *
     * @param ti        Current running thread.
     * @param ins       Insturction to be executed.
     * @param dynRegion Dynamic region that has been successfully transformed and summarized.
     */
    private static Instruction advanceSpf(ThreadInfo ti, Instruction ins, DynamicRegion dynRegion) {
        int endIns = dynRegion.endIns;
        while (ins.getPosition() != endIns) {
            if (ins instanceof GOTO && (((GOTO) ins).getTarget().getPosition() <= endIns))
                ins = ((GOTO) ins).getTarget();
            else ins = ins.getNext();
        }

        if (ins.getMnemonic().contains("store")) {
            ins = ins.getNext();
            System.out.println("advancing beyond a store at end of region");
        }
        //ti.setNextPC(ins);
        return ins;
    }

    /**
     * This is tries to discover statically all potential regions that could be used as veritesting regions.
     *
     * @param ti Current running thread.
     */
    private void discoverRegions(ThreadInfo ti) {
        Config conf = ti.getVM().getConfig();
        String classPath = conf.getStringArray("classpath")[0] + "/";
        String className = conf.getString("target");
        VeritestingMain veritestingMain = new VeritestingMain(ti, className + ".class");
        long startTime = System.nanoTime();
        veritestingMain.analyzeForVeritesting(classPath, className);
        long endTime = System.nanoTime();
        staticAnalysisDur = endTime - startTime;
    }


    public void publishFinished(Publisher publisher) {
        PrintWriter pw = publisher.getOut();
        publisher.publishTopicStart("VeritestingListener report:");
        long runEndTime = System.nanoTime();
        long dynRunTime = (runEndTime - runStartTime) - staticAnalysisDur;

        pw.println(statisticManager.printAllRegionStatistics());

        pw.println("\n/************************ Printing Time Decomposition Statistics *****************");
        pw.println("static analysis time = " + TimeUnit.NANOSECONDS.toMillis(staticAnalysisDur) + " msec");
        pw.println("Veritesting Dyn Time = " + TimeUnit.NANOSECONDS.toMillis(dynRunTime) + " msec");

        pw.println("\n/************************ Printing Solver Statistics *****************");
        pw.println("Total Solver Queries Count = " + solverCount);
        pw.println("Total Solver Time = " + TimeUnit.NANOSECONDS.toMillis(totalSolverTime) + " msec");
        pw.println("Total Solver Parse Time = " + TimeUnit.NANOSECONDS.toMillis(parseTime) + " msec");
        pw.println("Total Solver Clean up Time = " + TimeUnit.NANOSECONDS.toMillis(cleanupTime) + " msec");
        pw.println("SPFCaseSolverCount = " + StatisticManager.SPFCaseSolverCount);
        pw.println("SPFCaseSolverTime = " + TimeUnit.NANOSECONDS.toMillis(StatisticManager.SPFCaseSolverTime) + " msec");
        pw.println("Constant Propagation Time for PC sat. checks = " + TimeUnit.NANOSECONDS.toMillis(StatisticManager.constPropTime));
        pw.println("Array SPF Case count = " + StatisticManager.ArraySPFCaseCount);

        pw.println(statisticManager.printAccumulativeStatistics());

        pw.println("Total number of Distinct regions = " + statisticManager.regionCount());
        pw.println("Number of Veritested Regions Instances = " + veritestRegionCount);
        /* Begin added for equivalence checking */
        if (veritestRegionExpectedCount != -1) {
            pw.println("Expected Number of Veritested Regions Instances = " + veritestRegionExpectedCount);
            assert (veritestRegionCount == veritestRegionExpectedCount);
        }
        /* End added for equivalence checking */


        pw.println(TimeUnit.NANOSECONDS.toMillis(staticAnalysisDur)+","+
                TimeUnit.NANOSECONDS.toMillis(dynRunTime) + "," +
                solverCount + "," +
                TimeUnit.NANOSECONDS.toMillis(totalSolverTime) + "," +
                TimeUnit.NANOSECONDS.toMillis(parseTime) + "," +
                TimeUnit.NANOSECONDS.toMillis(cleanupTime) + "," +
                statisticManager.getDistinctVeriRegionNum() + "," +
                statisticManager.getDistinctSpfRegionNum() + "," +
                statisticManager.getConcreteRegionNum() + "," +
                statisticManager.getFailNum(FailEntry.FailReason.FIELDREFERNCEINSTRUCTION) + "," +
                statisticManager.getFailNum(FailEntry.FailReason.SPFCASEINSTRUCTION) + "," +
                statisticManager.getFailNum(FailEntry.FailReason.OTHER) + "," +
                hgOrdRegionInstance + "," +
                statisticManager.regionCount() + "," +
                veritestRegionCount);

    }
}
