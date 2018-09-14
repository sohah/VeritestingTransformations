package gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst;

import com.ibm.wala.ssa.IR;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import gov.nasa.jpf.symbc.veritesting.ast.def.Region;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.*;

/**
 * A class that represents a Static Region. That is a region that has been statically analyzed but has not been instantiated yet.
 */
public class StaticRegion implements Region {
    /**
     * Statement of the region.
     */
    public final Stmt staticStmt;

    /**
     * IR of the method that the StaticRegion belongs to.
     */
    public final IR ir;

    /**
     * An Environment table that holds a mapping from vars to either their stack slot position, in case of conditional regions, or to their parameter number in case of a MethodRegion.
     */
    public final Table slotParamTable;

    /**
     * An Environment table that holds the output of the region that needs to be popluated later to SPF upon successful veritesting. The output is computed as the last Phi for every stack slot.
     */
    public final Table outputTable;

    /**
     * this is the last instruction where SPF needs to start from after the region
     */
    public final int endIns;

    /**
     * A boolean that indicates whether this is a conditional region,i.e, a region that begins with an if instruction, or a method region, i.e., a region that is summarizing the whole method.
     */
    public final boolean isMethodRegion;

    /**
     * An environment table that defines the input vars to the region. it defines the mapping from slot/param to var
     */
    public final Table inputTable;

    /**
     * An environment table that holds the types of all vars defined inside the region.
     */
    public final VarTypeTable varTypeTable;

    public StaticRegion(Stmt staticStmt, IR ir, Boolean isMethodRegion, int endIns) {
        this.staticStmt = staticStmt;
        this.ir = ir;
        this.isMethodRegion = isMethodRegion;

        //Auxiliary vars to determine boundaries of different tables.
        Integer firstUse;
        Integer lastUse;
        Integer firstDef = null;
        Integer lastDef = null;
        Integer lastVar;


        if (isMethodRegion) {
            slotParamTable = new SlotParamTable(ir, isMethodRegion, staticStmt);
            varTypeTable = new VarTypeTable(ir);
        } else {
            Pair<Pair<Integer, Integer>, Pair<Integer, Integer>> regionBoundary = computeRegionBoundary(staticStmt);
            // first use var that hasn't been defined in the region, an invariant that this must be the first use in the if condition

            firstUse = regionBoundary.getFirst().getFirst();
            lastUse = regionBoundary.getFirst().getSecond();
            firstDef = regionBoundary.getSecond().getFirst();
            lastDef = regionBoundary.getSecond().getSecond();

            lastVar = ((lastDef != null) && (lastDef > lastUse)) ? lastDef: lastUse;

            slotParamTable = new SlotParamTable(ir, isMethodRegion, staticStmt, new Pair<>(firstUse, lastVar));
            varTypeTable = new VarTypeTable(ir, new Pair<>(firstUse, lastVar));
        }

        inputTable = new InputTable(ir, isMethodRegion, (SlotParamTable) slotParamTable, staticStmt);


        if (isMethodRegion) //no output in terms of slots can be defined for the method region, last statement is always a return and is used to conjunct it with the outer region.
            //outputTable = new OutputTable(ir, isMethodRegion, slotParamTable, inputTable, staticStmt);
            outputTable = new OutputTable(isMethodRegion);
        else {
            if (firstDef == null) //region has no def, so no output can be defined
                outputTable = new OutputTable(isMethodRegion);
            else
                outputTable = new OutputTable(ir, isMethodRegion, (SlotParamTable) slotParamTable, (InputTable) inputTable, staticStmt, new Pair<>(firstDef, lastDef));
        }
        this.endIns = endIns;
    }

    /**
     * This computes the region boundary in case of conditional region, to determine the first use and the first and last def variables inside the region.
     *
     * @param stmt Statement of the region.
     * @return A triple of first-use, first-def and last-def variables in the region.
     */
    private Pair<Pair<Integer, Integer>, Pair<Integer, Integer>> computeRegionBoundary(Stmt stmt) {
        ExprBoundaryVisitor exprBoundaryVisitor = new ExprBoundaryVisitor();

        RegionBoundaryVisitor regionBoundaryVisitor = new RegionBoundaryVisitor(exprBoundaryVisitor);
        stmt.accept(regionBoundaryVisitor);
        return new Pair<>(new Pair<>(regionBoundaryVisitor.getFirstUse(), regionBoundaryVisitor.getLastUse()), new Pair<>(regionBoundaryVisitor.getFirstDef(), regionBoundaryVisitor.getLastDef()));
    }
}
