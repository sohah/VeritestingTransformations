package gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment;

import gov.nasa.jpf.symbc.veritesting.ast.def.Region;
import gov.nasa.jpf.symbc.veritesting.ast.def.SPFCaseStmt;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticRegion;

import java.util.HashSet;

/**
 * This class represents a DynamicRegion, that is, a StaticRegion that has been instantiated.
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
    public final SlotParamTable slotParamTable;

    /**
     * An environment able that holds the vars that needs to be populate their summarized output to SPF.
     */
    public final OutputTable outputTable;

    /**
     * This holds the static version of the region that is matching this instantiation.
     */
    public final StaticRegion staticRegion;

    /**
     * An environment table tht holds the times of all vars in the region.
     */
    public final VarTypeTable varTypeTable;

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


    /**
     * Basic constructor that is used to construct the DynamicRegion for the first time out a StaticRegion.
     */

    public DynamicRegion(StaticRegion staticRegion,
                         Stmt dynStmt,
                         HashSet<SPFCaseStmt> spfCaseSet) {

        this.staticRegion = staticRegion;
        this.dynStmt = dynStmt;
        this.slotParamTable = staticRegion.slotParamTable.clone();
        this.outputTable = staticRegion.outputTable.clone();
        this.endIns = staticRegion.endIns;
        this.varTypeTable = staticRegion.varTypeTable.clone();
        this.isMethodRegion = staticRegion.isMethodRegion;
        this.spfCaseSet = spfCaseSet;
    }

    /**
     * A constructor that are later used multiple time when transforming one DynamicRegion to another.
     *
     */
    public DynamicRegion(StaticRegion staticRegion,
                         Stmt dynStmt,
                         VarTypeTable varTypeTable,
                         SlotParamTable slotParamTable,
                         OutputTable outputTable,
                         boolean isMethodRegion,
                         HashSet<SPFCaseStmt> spfCaseSet) {

        this.dynStmt = dynStmt;
        this.staticRegion = staticRegion;
        this.slotParamTable = slotParamTable;
        this.outputTable = outputTable;
        this.endIns = staticRegion.endIns;
        this.varTypeTable = varTypeTable;
        this.isMethodRegion = isMethodRegion;
        this.spfCaseSet = spfCaseSet;
    }
}
