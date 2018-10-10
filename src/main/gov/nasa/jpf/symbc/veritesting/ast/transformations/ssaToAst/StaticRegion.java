package gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst;

import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.ISSABasicBlock;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSAInstruction;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.SymbCondVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Invariants.LocalOutputInvariantVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitorAdapter;
import za.ac.sun.cs.green.expr.Expression;

import java.util.*;

import static java.util.Collections.reverse;

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
     * An environment table that holds the types of local variables defined inside the region.
     */
    public final VarTypeTable varTypeTable;

    /**
     * @param staticStmt: Ranger IR statement that summarizes this static region
     * @param ir: Wala IR for the method which contains this StaticRegion
     * @param isMethodRegion: boolean value that if true indicates that this StaticRegion is for a method summary
     * @param endIns: Ending instruction's bytecode offset for this static region
     * @param startingBlock: if given, startingBlock is used for constructing definitions for variables used in the
     *                     condition of the staticStmt, if the StaticRegion is for a multi-path region.
     *                     startingBlock should correspond to the beginning block of the region.
     *                     If unavailable, it can be given a null value.
     * @throws StaticRegionException
     */
    public StaticRegion(Stmt staticStmt, IR ir, Boolean isMethodRegion, int endIns, ISSABasicBlock startingBlock) throws StaticRegionException {

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
            slotParamTable = new SlotParamTable(ir, isMethodRegion, staticStmt, new Pair<>(-2147483647, 2147483646));
            SymbCondVisitor symbCondVisitor = new SymbCondVisitor(null, (SlotParamTable) slotParamTable, true);
            ExprVisitorAdapter eva = symbCondVisitor.eva;
            if(staticStmt instanceof CompositionStmt){
                eva.accept(((IfThenElseStmt)((CompositionStmt) staticStmt).s1).condition);
            }
            else if(staticStmt instanceof IfThenElseStmt) {
                eva.accept(((IfThenElseStmt) staticStmt).condition);
            }
            if (symbCondVisitor.stackSlotNotFound) {
                StaticRegionException sre = new StaticRegionException("region contains condition that cannot be instantiated");
                SSACFG cfg = ir.getControlFlowGraph();
                if (startingBlock == null) throw sre;
                ISSABasicBlock bb = startingBlock;
                boolean foundStoppingInsn = false;
                while (symbCondVisitor.noStackSlotVars.size() > 0 && !foundStoppingInsn) {
                    List<SSAInstruction> bbInsns = ((SSACFG.BasicBlock)bb).getAllInstructions();
                    reverse(bbInsns);
                    for (SSAInstruction ins : bbInsns) {
                        SSAToStatDefVisitor visitor =
                                new SSAToStatDefVisitor(ir, symbCondVisitor.noStackSlotVars, (SlotParamTable) slotParamTable);
                        Stmt stmt = visitor.convert(ins);
                        foundStoppingInsn = visitor.foundStoppingInsn;
                        if (stmt != null) {
                            staticStmt = new CompositionStmt(stmt, staticStmt);
                        }
                    }
                    Iterator itr = cfg.getPredNodes(bb);
                    if (cfg.getPredNodeCount(bb) != 1) foundStoppingInsn = true;
                    else bb = (ISSABasicBlock) itr.next();
                }
                if (symbCondVisitor.noStackSlotVars.size() > 0) {
                    throw sre;
                }
            }
            Pair<Pair<Integer, Integer>, Pair<Integer, Integer>> regionBoundary = computeRegionBoundary(staticStmt);
            // first use var that hasn't been defined in the region, an invariant that this must be the first use in the if condition

            firstUse = regionBoundary.getFirst().getFirst();
            lastUse = regionBoundary.getFirst().getSecond();
            firstDef = regionBoundary.getSecond().getFirst();
            lastDef = regionBoundary.getSecond().getSecond();

            lastVar = (lastDef != null) && (lastUse == null) ? lastDef : ((lastDef == null) && (lastUse != null) ? lastUse : (lastDef > lastUse ? lastDef: lastUse));
            ((SlotParamTable) slotParamTable).filterTableForBoundary(staticStmt, new Pair<>(firstUse, lastVar));
            varTypeTable = new VarTypeTable(ir, new Pair<>(firstUse, lastVar));
        }
        this.staticStmt = staticStmt;

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
        if (staticStmt instanceof CompositionStmt && ((CompositionStmt) staticStmt).s2 instanceof AssignmentStmt) {
            AssignmentStmt assignmentStmt = (AssignmentStmt) ((CompositionStmt) staticStmt).s2;
            if ((assignmentStmt.rhs instanceof GammaVarExpr) && (outputTable.table.size() == 0)) {
                throw new StaticRegionException("static region with gamma expression cannot have no local outputs");
            }
        }
        LocalOutputInvariantVisitor.execute(this);
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
