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
import gov.nasa.jpf.report.PublisherExtension;
import gov.nasa.jpf.symbc.numeric.*;
import gov.nasa.jpf.symbc.veritesting.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.AstToGreen.AstToGreenExprVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.AstToGreen.AstToGreenVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.SPFCases.SpfCasesVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Uniquness.UniqueRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.linearization.LinearizationTransformation;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.CreateStaticRegions;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.OutputTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution.SubstitutionVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.PrettyPrintVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.StmtPrintVisitor;
import gov.nasa.jpf.vm.*;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Operation;

import java.util.*;

import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.greenToSPFExpression;

public class VeritestingListener extends PropertyListenerAdapter implements PublisherExtension {


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
    public static final int maxStaticExplorationDepth = 2;
    public static boolean firstTime = true;


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
        if (firstTime) {
            discoverRegions(ti); // static analysis to discover regions
            firstTime = false;
        } else {
            MethodInfo methodInfo = instructionToExecute.getMethodInfo();
            String className = methodInfo.getClassName();
            String methodName = methodInfo.getName();
            String methodSignature = methodInfo.getSignature();
            int offset = instructionToExecute.getPosition();
            String key = CreateStaticRegions.constructRegionIdentifier(className + "." + methodName + methodSignature, offset);
            HashMap<String, StaticRegion> regionsMap = VeritestingMain.veriRegions;

            StaticRegion staticRegion = regionsMap.get(key);
            if(staticRegion != null){
                System.out.println("\n---------- STARTING Transformations for region: " + key +"\n" + PrettyPrintVisitor.print(staticRegion.staticStmt)+"\n");

                staticRegion.stackSlotTable.print();
                staticRegion.outputTable.print();
                staticRegion.inputTable.print();

                /*System.out.println("--------------- SPFCases TRANSFORMATION ---------------");
                staticRegion = SpfCasesVisitor.doSpfCases(staticRegion);
                System.out.println(StmtPrintVisitor.print(staticRegion.staticStmt));*/
                System.out.println("\n--------------- SUBSTITUTION TRANSFORMATION ---------------\n");
                DynamicRegion dynRegion = SubstitutionVisitor.doSubstitution(ti, staticRegion);
                System.out.println(StmtPrintVisitor.print(dynRegion.dynStmt));
                dynRegion.stackSlotTable.print();
                dynRegion.outputTable.print();
                dynRegion.valueSymbolTable.print();
                dynRegion.varTypeTable.print();


                System.out.println("--------------- UNIQUNESS TRANSFORMATION ---------------");
                dynRegion = UniqueRegion.doUniqueness(dynRegion);
                System.out.println(StmtPrintVisitor.print(dynRegion.dynStmt));
                dynRegion.stackSlotTable.print();
                dynRegion.valueSymbolTable.print();
                dynRegion.varTypeTable.print();
                dynRegion.outputTable.print();


                System.out.println("--------------- LINEARIZATION TRANSFORMATION ---------------");
                LinearizationTransformation linearTrans = new LinearizationTransformation();
                dynRegion = linearTrans.execute(dynRegion);
                System.out.println(StmtPrintVisitor.print(dynRegion.dynStmt));


                System.out.println("--------------- TO GREEN TRANSFORMATION ---------------");
                // populateSPF();
            }
        }
    }

    private void PopulateSPF(ThreadInfo ti, Instruction ins, DynamicRegion dynRegion, Expression regionSummary) {
        populateSlots(ti, dynRegion);
        updatePathCondition(ti, regionSummary);
        advanceSpf(ti, ins, dynRegion);
    }

    private void updatePathCondition(ThreadInfo ti, Expression regionSummary) {

        PathCondition pc;

        if (ti.getVM().getSystemState().getChoiceGenerator() instanceof PCChoiceGenerator)
            pc = ((PCChoiceGenerator)(ti.getVM().getSystemState().getChoiceGenerator())).getCurrentPC();
        else{
            pc = new PathCondition();
            pc._addDet(new GreenConstraint(Operation.TRUE));
        }
        pc._addDet(new GreenConstraint(regionSummary));
    }

    private void populateSlots(ThreadInfo ti, DynamicRegion dynRegion) {
        StackFrame sf = ti.getTopFrame();
        
        OutputTable outputTable = dynRegion.outputTable;
        Set<Integer> keys = outputTable.getKeys();

        Iterator itr = keys.iterator();
        Integer var;

        while(itr.hasNext()){
            Integer slot = (Integer) itr.next();
             var = outputTable.lookup(slot);
        //    sf.setSlotAttr(slot, greenToSPFExpression(new IntVariable()));
        }
    }

    private void advanceSpf(ThreadInfo ti, Instruction ins, DynamicRegion dynRegion) {
        Expression regionSummary; //= dynRegion.dynStmt.accept((new AstToGreenVisitor()));
        int endIns = dynRegion.endIns;
        while (ins.getPosition() != endIns) {
            if (ins instanceof GOTO && (((GOTO) ins).getTarget().getPosition() <= endIns))
                ins = ((GOTO) ins).getTarget();
            else ins = ins.getNext();
        }
        ti.setNextPC(ins);
    }


    private void discoverRegions(ThreadInfo ti) {
        Config conf = ti.getVM().getConfig();
        String classPath = conf.getStringArray("classpath")[0] + "/";
        String className = conf.getString("target");
        // should be like VeritestingPerf.testMe4([II)V aka jvm internal format
        VeritestingMain veritestingMain = new VeritestingMain(ti, className + ".class");
        long startTime = System.nanoTime();
        veritestingMain.analyzeForVeritesting(classPath, className);
        long endTime = System.nanoTime();
        long duration = (endTime - startTime) / 1000000; //milliseconds
        staticAnalysisTime = (endTime - startTime);
        System.out.println("veritesting analysis took " + duration + " milliseconds");
    }

}
