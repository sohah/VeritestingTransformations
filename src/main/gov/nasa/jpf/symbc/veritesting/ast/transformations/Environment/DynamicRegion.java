package gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment;

import com.ibm.wala.ssa.IR;
import gov.nasa.jpf.symbc.veritesting.ast.def.Region;
import gov.nasa.jpf.symbc.veritesting.ast.def.SPFCaseStmt;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticRegion;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Variable;

import java.util.HashMap;
import java.util.HashSet;

/**
 * This class represents a DynamicRegion, that is, a StaticRegion that has been processed dynamically, this is done initially through uniquness transformation then later with the substitution and other transformations.
 * A main difference in this data structure than the StaticRegion is that, the dynamic region now holds environment tables that have a unique name for every variable used.
 */
public class DynamicRegion implements Region {
    /**
     * unique counter used to maintain uniquness among vars in case a region was used multiple times, like in a loop.
     */
    public static int uniqueCounter = 0;

    /**
     * A statement that represents the region after instantiation.
     */
    public final Stmt dynStmt;

    /**
     * A table that holds the mapping of vars in the dynamic statement to their corresponding stack slot.
     */
    public final DynamicTable slotParamTable;


    /**
     * A table that holds inputs to the region.
     */
    public final DynamicTable inputTable;

    /**
     * An environment able that holds the vars that needs to be populate their summarized output to SPF.
     */
    public final DynamicOutputTable outputTable;

    /**
     * This holds the static version of the region that is matching this instantiation.
     */
    public final IR ir;

    /**
     * An environment table tht holds the times of all vars in the region.
     */
    public final DynamicTable varTypeTable;

    /**
     * Identifies the End Position that the region is summarizing and which also SPF to resume from.
     */
    public final int endIns;

    /**
     * Identifies if the dynamic region corresponds to a region that starts with a condition, or is it enclosing the summary of the whole method.
     */
    public final boolean isMethodRegion;

    /**
     * Holds all SPFCases predicates that are not statically summarized and are left for SPF to explore.
     */
    public final HashSet<SPFCaseStmt> spfCaseSet;

    public final Expression regionSummary;

/*

*/
/**
     * Basic constructor that is used to construct the DynamicRegion from another DynamicRegion, it also clones the tables of the old region.
     *//*


    public DynamicRegion(DynamicRegion oldDynRegion,
                         Stmt dynStmt,
                         HashSet<SPFCaseStmt> spfCaseSet, HashMap<Variable, Variable> varToVarMap) {
        this.ir = oldDynRegion.ir;
        this.dynStmt = dynStmt;
        this.inputTable = new DynamicTable(
                "Region Input Table",
                "var",
                oldDynRegion.isMethodRegion ? "param" : "slot");;
        this.endIns = oldDynRegion.endIns;
        this.isMethodRegion = oldDynRegion.isMethodRegion;
        this.outputTable = oldDynRegion.outputTable.clone(varToVarMap);
        this.varTypeTable = oldDynRegion.varTypeTable.clone(varToVarMap);
        this.slotParamTable = oldDynRegion.slotParamTable.clone(varToVarMap);
        this.spfCaseSet = spfCaseSet;
    }

*/


    public DynamicRegion(DynamicRegion oldDynRegion,
                         Stmt dynStmt,
                         HashSet<SPFCaseStmt> spfCaseSet,
                         Expression regionSummary) {
        this.ir = oldDynRegion.ir;
        this.dynStmt = dynStmt;
        this.inputTable = new DynamicTable(
                "Region Input Table",
                "var",
                oldDynRegion.isMethodRegion ? "param" : "slot");;
        this.endIns = oldDynRegion.endIns;
        this.isMethodRegion = oldDynRegion.isMethodRegion;
        this.outputTable = oldDynRegion.outputTable;
        this.varTypeTable = oldDynRegion.varTypeTable;
        this.slotParamTable = oldDynRegion.slotParamTable;
        this.spfCaseSet = spfCaseSet;
        this.regionSummary = regionSummary;
    }



    /**
     * Constructor that is used to create a dynamic region out of a static region.
     * @param staticRegion
     * @param dynStmt
     * @param varToNumMap
     */

    public DynamicRegion(StaticRegion staticRegion, Stmt dynStmt, HashMap<Integer, Variable> varToNumMap) {
        this.ir = staticRegion.ir;
        this.dynStmt = dynStmt;
        this.endIns = staticRegion.endIns;
        this.isMethodRegion = staticRegion.isMethodRegion;
        this.spfCaseSet = new HashSet<>();
        this.regionSummary = null;

        this.slotParamTable = new DynamicTable(
                (StaticTable) staticRegion.slotParamTable,
                varToNumMap,
                "stack-slot table",
                "var",
                staticRegion.isMethodRegion ? "param" : "slot");

        this.inputTable = new DynamicTable(
                (StaticTable)staticRegion.inputTable,
                varToNumMap,
                "Region Input Table",
                "var",
                staticRegion.isMethodRegion ? "param" : "slot");

        this.varTypeTable = new DynamicTable(
                (StaticTable)staticRegion.varTypeTable,
                varToNumMap,
                "WalaVarTypeTable",
                " var ",
                "type");

        this.outputTable = new DynamicOutputTable(
                (OutputTable) staticRegion.outputTable,
                varToNumMap,
                "Region Output Table",
                staticRegion.isMethodRegion ? "return" : "slot",
                "var");

    }
}
