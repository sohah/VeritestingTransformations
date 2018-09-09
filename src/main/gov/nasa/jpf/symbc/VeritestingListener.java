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
import gov.nasa.jpf.jvm.bytecode.GOTO;
import gov.nasa.jpf.report.ConsolePublisher;
import gov.nasa.jpf.report.Publisher;
import gov.nasa.jpf.report.PublisherExtension;
import gov.nasa.jpf.symbc.numeric.*;
import gov.nasa.jpf.symbc.veritesting.*;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.SpfUtil;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.AstToGreen.AstToGreenVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Uniquness.UniqueRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.fieldaccess.FieldSSAVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.linearization.LinearizationTransformation;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.CreateStaticRegions;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.OutputTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution.SubstitutionVisitor;

import gov.nasa.jpf.symbc.veritesting.ast.transformations.typepropagation.TypePropagationVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.PrettyPrintVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.StmtPrintVisitor;
import gov.nasa.jpf.vm.*;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Operation;

import java.io.PrintWriter;
import java.util.*;
import java.util.concurrent.TimeUnit;

import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.createGreenVar;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.greenToSPFExpression;

public class VeritestingListener extends PropertyListenerAdapter implements PublisherExtension {


    //TODO: make these into configuration options
    public static int veritestingMode = 0;

    public static long totalSolverTime = 0, z3Time = 0;
    public static long parseTime = 0;
    public static long solverAllocTime = 0;
    public static long cleanupTime = 0;
    public static int solverCount = 0;
    public static int unsatSPFCaseCount = 0;
    public static final int maxStaticExplorationDepth = 2;
    public static boolean firstTime = true;
    private static long staticAnalysisDur;
    private  final long runStartTime = System.nanoTime();


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

    /**
     * Listener's main method that checks every instruction for being a potential veritesting region.
     *
     * @param vm                   Virtual Machine.
     * @param ti                   Current running Thread.
     * @param instructionToExecute instruction to be executed.
     */
    public void executeInstruction(VM vm, ThreadInfo ti, Instruction instructionToExecute) {

        if (veritestingMode == 0) return;
        if (firstTime) {
            discoverRegions(ti); // static analysis to discover regions
            firstTime = false;
        } else {
            try {

                MethodInfo methodInfo = instructionToExecute.getMethodInfo();
                String className = methodInfo.getClassName();
                String methodName = methodInfo.getName();
                String methodSignature = methodInfo.getSignature();
                int offset = instructionToExecute.getPosition();
                String key = CreateStaticRegions.constructRegionIdentifier(className + "." + methodName + methodSignature, offset);
                HashMap<String, StaticRegion> regionsMap = VeritestingMain.veriRegions;

                StaticRegion staticRegion = regionsMap.get(key);
                if ((staticRegion != null) && !(staticRegion.isMethodRegion))
                    //if (SpfUtil.isSymCond(staticRegion.staticStmt)) {
                    if (SpfUtil.isSymCond(ti.getTopFrame(), staticRegion.slotParamTable, staticRegion.staticStmt)) {
                        System.out.println("\n---------- STARTING Transformations for region: " + key + "\n" + PrettyPrintVisitor.print(staticRegion.staticStmt) + "\n");
                        staticRegion.slotParamTable.print();
                        staticRegion.outputTable.print();
                        staticRegion.inputTable.print();

                        System.out.println("\n--------------- SUBSTITUTION TRANSFORMATION ---------------\n");
                        DynamicRegion dynRegion = SubstitutionVisitor.execute(ti, staticRegion);
                        System.out.println(StmtPrintVisitor.print(dynRegion.dynStmt));
                        dynRegion.slotParamTable.print();
                        dynRegion.outputTable.print();

                        // 1. Replace GetInstruction, PutInstruction by AssignmentStmt with a FieldAccessTriple on rhs or lhs resp.
                        // 2. Perform substitution on field references
                        // 3. Populate the PSM for every statement in the region
                        // 4. Create gamma expressions for field access
                        // 5 Propagate type information across operations
                        System.out.println("\n--------------- FIELD REFERENCE TRANSFORMATION ---------------\n");
                        dynRegion = FieldSSAVisitor.execute(ti, dynRegion);
//                        dynRegion = GetSubstitutionVisitor.execute(ti, dynRegion);
                        TypePropagationVisitor.propagateTypes(dynRegion);
                        System.out.println(StmtPrintVisitor.print(dynRegion.dynStmt));
                        dynRegion.fieldRefTypeTable.print();

                        System.out.println("\n--------------- UNIQUENESS TRANSFORMATION ---------------");
                        dynRegion = UniqueRegion.execute(dynRegion);
                        System.out.println(StmtPrintVisitor.print(dynRegion.dynStmt));
                        dynRegion.slotParamTable.print();
                        dynRegion.varTypeTable.print();
                        dynRegion.outputTable.print();

/*
                        System.out.println("--------------- SPFCases TRANSFORMATION 1ST PASS ---------------");
                        dynRegion = SpfCasesPass1Visitor.execute(ti, dynRegion);
                        System.out.println(StmtPrintVisitor.print(dynRegion.dynStmt));

                        System.out.println("--------------- SPFCases TRANSFORMATION 2ND PASS ---------------");
                        dynRegion = SpfCasesPass2Visitor.execute(dynRegion);
                        System.out.println(StmtPrintVisitor.print(dynRegion.dynStmt));
*/
                        System.out.println("\n--------------- LINEARIZATION TRANSFORMATION ---------------");
                        LinearizationTransformation linearTrans = new LinearizationTransformation();
                        dynRegion = linearTrans.execute(dynRegion);
                        System.out.println(StmtPrintVisitor.print(dynRegion.dynStmt));

                        System.out.println("\n--------------- TO GREEN TRANSFORMATION ---------------");
                        Expression regionSummary = AstToGreenVisitor.execut(dynRegion);
                        /*System.out.println(ExprUtil.AstToString(regionSummary));*/
                        setupSPF(ti, instructionToExecute, dynRegion, regionSummary);
                    }
            } catch (IllegalArgumentException e) {
                System.out.println("!!!!!!!! Aborting Veritesting !!!!!!!!!!!! " + "\n" + e.getMessage() + "\n");
                return;
            } catch (StaticRegionException sre) {
                System.out.println("!!!!!!!! Aborting Veritesting !!!!!!!!!!!! " + "\n" + sre.getMessage() + "\n");
                return;
            } catch (CloneNotSupportedException e) {
                System.out.println("!!!!!!!! Aborting Veritesting !!!!!!!!!!!! " + "\n" + e.getMessage() + "\n");
                e.printStackTrace();
                return;
            }
        }
    }

    /**
     * This populates the Output of the summarized region to SPF.
     *
     * @param ti            Currently running thread.
     * @param ins           Branch instruction that indicates beginning of the region.
     * @param dynRegion     Dynamic region that has been summarized.
     * @param regionSummary Final summary of the region, after all transformations has been successfully completed.
     * @throws StaticRegionException Exception to indicate a problem while setting SPF.
     */

    private void setupSPF(ThreadInfo ti, Instruction ins, DynamicRegion dynRegion, Expression regionSummary) throws StaticRegionException {
        if (canSetPC(ti, regionSummary)) {
            populateSlots(ti, dynRegion);
            clearStack(ti.getModifiableTopFrame(), ins);
            advanceSpf(ti, ins, dynRegion);
        }
    }

    /**
     * This method checks that the current PathCondition and after appending the summarized region is satisfiable.
     *
     * @param ti            Currently running thread.
     * @param regionSummary Finaly summary of the region, after all transformations has been successfully completed.
     * @return PathCondition is still satisfiable or not.
     * @throws StaticRegionException Exception to indicate a problem while checking SAT of the updated PathCondition.
     */
    private boolean canSetPC(ThreadInfo ti, Expression regionSummary) throws StaticRegionException {
        PathCondition pc;

        if (ti.getVM().getSystemState().getChoiceGenerator() instanceof PCChoiceGenerator)
            pc = ((PCChoiceGenerator) (ti.getVM().getSystemState().getChoiceGenerator())).getCurrentPC();
        else {
            pc = new PathCondition();
            pc._addDet(new GreenConstraint(Operation.TRUE));
        }
        pc._addDet(new GreenConstraint(regionSummary));
        if (pc.simplify()) {
            ((PCChoiceGenerator) ti.getVM().getSystemState().getChoiceGenerator()).setCurrentPC(pc);
            return true;
        } else {
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
    private void clearStack(StackFrame sf, Instruction ins) throws StaticRegionException {
        int numOperands = SpfUtil.getOperandNumber(ins.getMnemonic());
        while (numOperands > 0) {
            sf.pop();
            numOperands--;
        }
    }

    /**
     * Populates SPF stack slot with the output of the veritesting region.
     *
     * @param ti        Current executing thread.
     * @param dynRegion Dynamic region that has been successfully transformed and summarized.
     */
    private void populateSlots(ThreadInfo ti, DynamicRegion dynRegion) {
        StackFrame sf = ti.getTopFrame();
        OutputTable outputTable = dynRegion.outputTable;
        Set<Integer> slots = outputTable.getKeys();

        Iterator slotItr = slots.iterator();

        while (slotItr.hasNext()) {
            Integer slot = (Integer) slotItr.next();
            String varId = "w" + Integer.toString(outputTable.lookup(slot));
            Expression symVar = createGreenVar(dynRegion.varTypeTable.lookup(outputTable.lookup(slot)), varId);
            sf.setSlotAttr(slot, greenToSPFExpression(symVar));
        }
    }

    /**
     * Steps SPF to the end of the region.
     *
     * @param ti        Current running thread.
     * @param ins       Insturction to be executed.
     * @param dynRegion Dynamic region that has been successfully transformed and summarized.
     */
    private void advanceSpf(ThreadInfo ti, Instruction ins, DynamicRegion dynRegion) {
        int endIns = dynRegion.endIns;
        while (ins.getPosition() != endIns) {
            if (ins instanceof GOTO && (((GOTO) ins).getTarget().getPosition() <= endIns))
                ins = ((GOTO) ins).getTarget();
            else ins = ins.getNext();
        }
        ti.setNextPC(ins);
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
        pw.println("static analysis time = " + TimeUnit.NANOSECONDS.toMillis(staticAnalysisDur) + " msec");
        pw.println("# regions = " + VeritestingMain.veriRegions.size());
        long runEndTime = System.nanoTime();
        long dynRunTime = (runEndTime - runStartTime) - staticAnalysisDur;
        pw.print("Veritesting Dyn Time = " + TimeUnit.NANOSECONDS.toMillis(dynRunTime) + " msec");
    }
}
