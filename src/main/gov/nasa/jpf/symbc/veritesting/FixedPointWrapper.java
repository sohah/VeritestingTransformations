package gov.nasa.jpf.symbc.veritesting;

import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.SPFCases.SPFCaseList;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.arrayaccess.ArraySSAVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.constprop.SimplifyStmtVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.fieldaccess.FieldSSAVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution.SubstitutionVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.FixedPointAstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.StmtPrintVisitor;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Variable;

import java.util.Iterator;
import java.util.Map;

/**
 * This class is called multiple times over different transformations. What it does is that it keeps a common state among all
 * transformations, that is was called on.
 */

public class FixedPointWrapper {


    public static DynamicRegion getRegionAfter() {
        return regionAfter;
    }

    enum Transformation {SUBSTITUTION, FIELD, ARRAY};

    /**
     * Tells if there has been a change
     */
    private static boolean changed = false;

    /**
     * Tells which transformation is responsible for the change, thi carries the first transformation that has happened.
     */
    private static Transformation changedTransformation = null;

    /**
     * Keeps the first exception that has been encountered in all the transformations.
     */
    private static Exception firstException = null;

    private static ThreadInfo ti = null;

    private static StackFrame topStackFrame = null;

    private static DynamicRegion regionBefore = null;

    private static DynamicRegion regionAfter = null;

    private static int iterationNumber = 0;

    /**
     * Returns if change has happened
     * @return
     */
    public static boolean isChangedFlag() {
        return changed;
    }

    public static boolean isEqualRegion(){
        return regionBefore.dynStmt.equals(regionAfter.dynStmt);
    }

    public static Exception getFirstException() {
        return firstException;
    }

    public static int getIterationNumber() {
        return iterationNumber;
    }

    public static Transformation getChangedTransformation(){
        return changedTransformation;
    }


    /**
     * sets if change has happened and also sets up the transformation responsible for the change;
     *
     */
    private static void collectTransformationState(FixedPointAstMapVisitor currentTransformation) {
        boolean transformationChange = currentTransformation.getChange();
        if(!isChangedFlag()){
            FixedPointWrapper.changed = transformationChange;

            if(currentTransformation instanceof SubstitutionVisitor)
            changedTransformation = Transformation.SUBSTITUTION;
        else if(currentTransformation instanceof FieldSSAVisitor)
            changedTransformation = Transformation.FIELD;
        else if(currentTransformation instanceof ArraySSAVisitor)
            changedTransformation = Transformation.ARRAY;
        else
            assert false;
        }

        Exception transformationException = currentTransformation.getFirstException();
        if(firstException == null)
            if(currentTransformation instanceof SubstitutionVisitor)
                firstException = transformationException;
    }

    public static void reset(){
        changed = false;
        changedTransformation = null;
        firstException = null;
    }

    public static DynamicRegion executeFixedPointTransformations(ThreadInfo ti, DynamicRegion dynRegion) throws StaticRegionException, CloneNotSupportedException {
        FixedPointWrapper.ti = ti;
        FixedPointWrapper.topStackFrame = ti.getTopFrame();
        FixedPointWrapper.regionBefore = dynRegion;
        DynamicRegion intermediateRegion;
        ++FixedPointWrapper.iterationNumber;
        if (FixedPointWrapper.iterationNumber > 1)
            FixedPointWrapper.reset();

        SubstitutionVisitor substitutionVisitor = SubstitutionVisitor.create(ti, dynRegion, iterationNumber);
        intermediateRegion = substitutionVisitor.execute();
        collectTransformationState(substitutionVisitor);


        System.out.println("\n--------------- FIELD REFERENCE TRANSFORMATION ---------------\n");
        FieldSSAVisitor fieldSSAVisitor = new FieldSSAVisitor(ti, dynRegion);
        Stmt fieldStmt = dynRegion.dynStmt.accept(fieldSSAVisitor);
        if (fieldSSAVisitor.exception != null && thisException == null) thisException = fieldSSAVisitor.exception;
        dynRegion.psm = fieldSSAVisitor.psm;
        dynRegion = new DynamicRegion(dynRegion, fieldStmt, new SPFCaseList(), null, null);

            /* Array substitution iteration */
        System.out.println("\n--------------- ARRAY TRANSFORMATION ---------------\n");
        ArraySSAVisitor arraySSAVisitor = new ArraySSAVisitor(ti, dynRegion);
        Stmt arrayStmt = dynRegion.dynStmt.accept(arraySSAVisitor);
        if (arraySSAVisitor.exception != null && thisException == null) thisException = arraySSAVisitor.exception;
        dynRegion.arrayOutputs = arraySSAVisitor.arrayExpressions;
        dynRegion = new DynamicRegion(dynRegion, arrayStmt, new SPFCaseList(), null, null);
        System.out.println(StmtPrintVisitor.print(dynRegion.dynStmt));
        System.out.println(dynRegion.arrayOutputs);

            /* Simplification iteration */
        DynamicTable<Expression> constantsTable = new DynamicTable<>("Constants Table", "Expression", "Constant Value");
        SimplifyStmtVisitor simplifyVisitor = new SimplifyStmtVisitor(dynRegion, constantsTable);
        Stmt simplifiedStmt = dynRegion.dynStmt.accept(simplifyVisitor);
        if (simplifyVisitor.getExprException() != null && thisException == null)
            thisException = simplifyVisitor.getExprException();
        if (dynRegion.constantsTable == null)
            dynRegion.constantsTable = simplifyVisitor.constantsTable;
        else dynRegion.constantsTable.addAll(simplifyVisitor.constantsTable);
//            simplifyArrayOutputs(dynRegion);
        dynRegion = new DynamicRegion(dynRegion, simplifiedStmt, dynRegion.spfCaseList, dynRegion.regionSummary,
                dynRegion.spfPredicateSummary);
        System.out.println("\n--------------- AFTER SIMPLIFICATION ---------------\n");
        System.out.println(StmtPrintVisitor.print(dynRegion.dynStmt));
        Iterator<Map.Entry<Variable, Expression>> itr = dynRegion.constantsTable.table.entrySet().iterator();
        System.out.println("Constants Table:");
        while (itr.hasNext()) {
            Map.Entry<Variable, Expression> entry = itr.next();
            System.out.println(entry.getKey() + ": " + entry.getValue());
        }


        regionAfter = intermediateRegion;
        return regionAfter;
    }


}
