package gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst;

import com.ibm.wala.cfg.Util;
import com.ibm.wala.ssa.*;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.Expr;
import gov.nasa.jpf.symbc.veritesting.ast.def.WalaComparisonExpr;
import gov.nasa.jpf.symbc.veritesting.ast.def.CompositionStmt;
import gov.nasa.jpf.symbc.veritesting.ast.def.IfThenElseStmt;
import gov.nasa.jpf.symbc.veritesting.ast.def.SkipStmt;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution.Region;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.PrettyPrintVisitor;

import java.util.HashMap;
import java.util.HashSet;

/*
    This class creates our structure IR from the WALA SSA form for further transformation.
    Right now it emits a string because the IR is not yet finished.

    Important question: what is the scope of this class?  Is it supposed to be maintained
    throughout the creation process or is it constructed / destructed for each visited method?

    In examining the debug output, it appears that the same classes and methods are visited
    multiple times.

 */

public class CreateStaticRegions {

    public CreateStaticRegions() {
        visitedBlocks = new HashSet<>();
    }


    public static String constructRegionIdentifier(String className, String methodName, String methodSignature, int offset) {
        return className + "." + methodName + methodSignature + "#" + offset;
    }

    public static String constructRegionIdentifier(ISSABasicBlock blk) {
        return constructRegionIdentifier(blk.getClass().getCanonicalName(),
                blk.getMethod().getName().toString(),
                blk.getMethod().getSignature(),
                blk.getFirstInstructionIndex());
    }

    public static String constructMethodIdentifier(String className, String methodName, String methodSignature) {
        return className + "." + methodName + methodSignature;
    }

    public static String constructMethodIdentifier(ISSABasicBlock blk) {
        return constructMethodIdentifier(blk.getClass().getCanonicalName(),
                blk.getMethod().getName().toString(),
                blk.getMethod().getSignature());
    }

    public boolean isBranch(SSACFG cfg, ISSABasicBlock block) {
        return cfg.getNormalSuccessors(block).size() == 2;
    }

    // for memoization.
    HashSet<ISSABasicBlock> visitedBlocks;


    public Stmt conjoin(Stmt stmt1, Stmt stmt2) {
        if (stmt1 instanceof SkipStmt) {
            return stmt2;
        } else if (stmt2 instanceof SkipStmt) {
            return stmt1;
        } else {
            return new CompositionStmt(stmt1, stmt2);
        }
    }

    private Stmt translateTruncatedFinalBlock(ISSABasicBlock currentBlock) throws StaticRegionException {
        Stmt stmt = SkipStmt.skip;
        for (SSAInstruction ins: currentBlock) {
            if (!(ins instanceof SSAPhiInstruction))
                return stmt;
            else {
                stmt = conjoin(stmt, SSAToStatIVisitor.convert(ins));
            }
        }
        return stmt;
    }

    private Stmt translateInternalBlock(ISSABasicBlock currentBlock) throws StaticRegionException {
        Stmt stmt = SkipStmt.skip;
        for (SSAInstruction ins: currentBlock) {
            if ((ins instanceof SSAConditionalBranchInstruction) ||
                    (ins instanceof SSAGotoInstruction)) {
                // properly formed blocks will only have branches and gotos as the last instruction.
                // We will handle branches in attemptSubregion.
            } else {
                stmt = conjoin(stmt, SSAToStatIVisitor.convert(ins));
            }
        }
        return stmt;
    }

    private Expr convertCondition(SSAConditionalBranchInstruction cond) {
        return new WalaComparisonExpr(cond);
    }

    // precondiion: terminus is the loop join.
    private Stmt conditionalBranch(SSACFG cfg, ISSABasicBlock currentBlock, ISSABasicBlock terminus) throws StaticRegionException {

        SSAInstruction ins = currentBlock.getLastInstruction();
        if (!(ins instanceof SSAConditionalBranchInstruction)) {
            throw new StaticRegionException("Expect conditional branch at end of 2-path attemptSubregion");
        }
        // Handle case where terminus is either 'if' or 'else' branch;
        Expr condExpr = convertCondition((SSAConditionalBranchInstruction)ins);
        ISSABasicBlock thenBlock = Util.getTakenSuccessor(cfg, currentBlock);
        Stmt thenStmt, elseStmt;
        if (thenBlock.getNumber() < terminus.getNumber()) {
            thenStmt = attemptSubregionRec(cfg, thenBlock, terminus);
        } else {
            thenStmt = SkipStmt.skip;
        }
        ISSABasicBlock elseBlock = Util.getNotTakenSuccessor(cfg, currentBlock);
        if (elseBlock.getNumber() < terminus.getNumber()) {
            elseStmt = attemptSubregionRec(cfg, elseBlock, terminus);
        } else {
            elseStmt = SkipStmt.skip;
        }

        return new IfThenElseStmt((SSAConditionalBranchInstruction) ins, condExpr, thenStmt, elseStmt);
    }

    /*
        This method translates from currentBlock up to but not including endingBlock.
        Doing it this way makes it much simpler to deal with nested if/then/elses that land in the same spot.

        It also makes it simpler to tailor the end of the translation: for methods, we want to grab the
        remaining code within the method, while for conditional blocks we only want to grab the subsequent \phi
        functions.

     */

    public Stmt attemptSubregionRec(SSACFG cfg, ISSABasicBlock currentBlock, ISSABasicBlock endingBlock) throws StaticRegionException {

        if (currentBlock == endingBlock) {
            return SkipStmt.skip;
        }

        Stmt stmt = translateInternalBlock(currentBlock);

        if (cfg.getNormalSuccessors(currentBlock).size() == 2) {
            FindStructuredBlockEndNode finder = new FindStructuredBlockEndNode(cfg, currentBlock, endingBlock);
            ISSABasicBlock terminus = finder.findMinConvergingNode();
            stmt = conjoin(stmt, conditionalBranch(cfg, currentBlock, terminus));
            stmt = conjoin(stmt, attemptSubregionRec(cfg, terminus, endingBlock));
        }
        else if (cfg.getNormalSuccessors(currentBlock).size() == 1){
            SSAInstruction last = (currentBlock.iterator().hasNext()) ? currentBlock.getLastInstruction() : null;

            // gets rid of a few extra 'skips'
            ISSABasicBlock nextBlock = cfg.getNormalSuccessors(currentBlock).iterator().next();
            if (nextBlock.getNumber() < endingBlock.getNumber()) {
                stmt = conjoin(stmt, attemptSubregionRec(cfg, nextBlock, endingBlock));
            }
        }
        return stmt;
    }

    // precondition: endingBlock is the terminus of the loop
    private Stmt attemptConditionalSubregion(SSACFG cfg, ISSABasicBlock startingBlock, ISSABasicBlock terminus) throws StaticRegionException {

        assert(isBranch(cfg, startingBlock));
        Stmt stmt = conditionalBranch(cfg, startingBlock, terminus);
        stmt = conjoin(stmt, translateTruncatedFinalBlock(terminus));
        return stmt;
    }

    private Stmt attemptMethodSubregion(SSACFG cfg, ISSABasicBlock startingBlock, ISSABasicBlock endingBlock) throws StaticRegionException {
        Stmt stmt = attemptSubregionRec(cfg, startingBlock, endingBlock);
        stmt = conjoin(stmt, translateInternalBlock(endingBlock));
        return stmt;
    }

    private void createStructuredConditionalRegions(IR ir, ISSABasicBlock currentBlock,
                                                   ISSABasicBlock endingBlock,
                                                   HashMap<String, Region> veritestingRegions) throws StaticRegionException {

        SSACFG cfg = ir.getControlFlowGraph();
        // terminating conditions
        if (visitedBlocks.contains(currentBlock))
            return;
        if (currentBlock == endingBlock) { return; }

        visitedBlocks.add(currentBlock);

        if (isBranch(cfg, currentBlock)) {
            try {
                FindStructuredBlockEndNode finder = new FindStructuredBlockEndNode(cfg, currentBlock, endingBlock);
                ISSABasicBlock terminus = finder.findMinConvergingNode();
                Stmt s = attemptConditionalSubregion(cfg, currentBlock, terminus);
                veritestingRegions.put(CreateStaticRegions.constructRegionIdentifier(currentBlock), new Region(s, ir));
                System.out.println("Subregion: " + System.lineSeparator() + PrettyPrintVisitor.print(s));

                createStructuredConditionalRegions(ir, terminus, endingBlock, veritestingRegions);
                return;
            } catch (StaticRegionException sre) {
                System.out.println("Unable to create subregion");
            }
        }
        for (ISSABasicBlock nextBlock: cfg.getNormalSuccessors(currentBlock)) {
            createStructuredConditionalRegions(ir, nextBlock, endingBlock, veritestingRegions);
        }
    }


    public void createStructuredConditionalRegions(IR ir, HashMap<String, Region> veritestingRegions) throws StaticRegionException {
        SSACFG cfg = ir.getControlFlowGraph();
        createStructuredConditionalRegions(ir, cfg.entry(), cfg.exit(), veritestingRegions);
    }

    public void createStructuredMethodRegion(IR ir, HashMap<String, Region> veritestingRegions) throws StaticRegionException {
        SSACFG cfg = ir.getControlFlowGraph();
        try {
            Stmt s = attemptMethodSubregion(cfg, cfg.entry(), cfg.exit());
            System.out.println("Method" + System.lineSeparator() + PrettyPrintVisitor.print(s));

            veritestingRegions.put(CreateStaticRegions.constructMethodIdentifier(cfg.entry()), new Region(s, ir));
        } catch (StaticRegionException sre) {
            System.out.println("Unable to create a method summary subregion for: " + cfg.getMethod().getName().toString());
        }
    }
}
