package gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst;

import com.ibm.wala.cfg.Util;
import com.ibm.wala.classLoader.IBytecodeMethod;
import com.ibm.wala.shrikeBT.IConditionalBranchInstruction;
import com.ibm.wala.shrikeCT.InvalidClassFileException;
import com.ibm.wala.ssa.*;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.SSAToStatIVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.PrettyPrintVisitor;
import za.ac.sun.cs.green.expr.*;

import java.util.*;

/*
    This class creates our structure IR from the WALA SSA form for further transformation.
    Right now it emits a string because the IR is not yet finished.

    Important question: what is the scope of this class?  Is it supposed to be maintained
    throughout the creation process or is it constructed / destructed for each visited method?
        Each method - the cfg changes.

    TODO: In examining the debug output, it appears that the same classes and methods are visited multiple times.  Why?

    The tricky bit involves translating \phi instructions to \gammas.
    Here’s how it works:

    I keep track of the current "conditional path" at the point of the code I am translating.  This is a stack of
    (Expression x enum {Then, Else}) pairs.  For each edge between blocks in the block structure,
    I record the associated "conditional path".  So the type of this map (the blockConditionMap) is:
        (ISSABasicBlock x ISSABasicBlock) --> List of (Expression x enum {Then, Else})

    From here it is easy: I get the predecessor blocks of the block containing the \phi.  Then I look
    up the edges in the blockConditionMap.  From here, I know the condition stack leading to that
    branch.  I gather these together and make an if/then/else.

    If I see something like this:
    \phi(w2, w8, w16)

    ==> I look up predecessor blocks:
      (1, 5, 8)

    ==> I look up associated conditions from predecessor edges:
      (((c1, Then)),
       ((c1, Else), (c2, Then)),
       ((c1, Else), (c2, Else)))

    then construct an if/then/else from the result.

    Two things that make it slightly more interesting:
    1.) What about \phis for the merge of inner (nested) branches?  Since I record a stack of
        conditions from the beginning of the static region, I don't really want the conditions
        from branches that are out of scope of the inner branch.  At the meet block, I check the
        conditionStack depth, and remove that depth of elements from the front of each condition list.

    2.) How does one arrange subconditions in the if/then/else to minimize the size of conditions?
        This is why I keep track of whether the condition corresponds to the 'then' or 'else' branch.
        I do a split based on 'then' or 'else' and recursively organize the Gamma.  For example,
        the Gamma for the example above would be:
        Gamma(c1, w2, Gamma(c2, w8, w16)))

        I could do this with just the expressions, but it would be much more work to reconstruct
        the then and else branches (in fact I started with this and then wasted substantial time
        trying to rebuild the minimal ITE structure.  Shame on me.

 */

public class CreateStaticRegions {

    public static String constructRegionIdentifier(String methodSignature, int offset) {
        return methodSignature + "#" + offset;
    }

    public static String constructRegionIdentifier(IR ir, ISSABasicBlock blk) {
        int offset = -100;
        try {
            offset = ((IBytecodeMethod) (ir.getMethod())).getBytecodeIndex(blk.getLastInstructionIndex());
        } catch (InvalidClassFileException e) {
            e.printStackTrace();
        }
        if(offset == -100)
            try {
                throw new StaticRegionException("Cannot find the index of the first instruction in the region.");
            } catch (StaticRegionException e) {
                e.printStackTrace();
            }

        return constructRegionIdentifier(blk.getMethod().getSignature(), offset);
    }

    public static String constructMethodIdentifier(String methodSignature) {
        return methodSignature;
    }

    public static String constructMethodIdentifier(ISSABasicBlock blk) {
        return constructMethodIdentifier(blk.getMethod().getSignature());
    }

    /*
        For Phi instructions!
     */


    private HashMap<PhiEdge, List<PhiCondition>> blockConditionMap;
    private Deque<PhiCondition> currentCondition;
    private IR ir;


    public CreateStaticRegions(IR ir) {
        blockConditionMap = new HashMap<>();
        currentCondition = new LinkedList<>();
        this.ir = ir;
    }

    private void reset() {
        blockConditionMap = new HashMap<>();
        currentCondition = new LinkedList<>();
    }

    public boolean isBranch(SSACFG cfg, ISSABasicBlock block) {
        return cfg.getNormalSuccessors(block).size() == 2;
    }


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
        SSAToStatIVisitor visitor =
                new SSAToStatIVisitor(ir, currentBlock, blockConditionMap, currentCondition);
        Stmt stmt = SkipStmt.skip;
        for (SSAInstruction ins: currentBlock) {
            if (!(ins instanceof SSAPhiInstruction))
                return stmt;
            else {
                Stmt gamma = visitor.convert(ins);
                stmt = conjoin(stmt, gamma);
            }
        }
        return stmt;
    }

    private Stmt translateInternalBlock(ISSABasicBlock currentBlock) throws StaticRegionException {
        SSAToStatIVisitor visitor =
                new SSAToStatIVisitor(ir, currentBlock, blockConditionMap, currentCondition);
        Stmt stmt = SkipStmt.skip;
        for (SSAInstruction ins: currentBlock) {
            if ((ins instanceof SSAConditionalBranchInstruction) ||
                    (ins instanceof SSAGotoInstruction)) {
                // properly formed blocks will only have branches and gotos as the last instruction.
                // We will handle branches in attemptSubregion.
            } else {
                stmt = conjoin(stmt, visitor.convert(ins));
            }
        }
        return stmt;
    }

    private Operation.Operator convertOperator(IConditionalBranchInstruction.Operator operator) {
        switch (operator) {
            case EQ: return Operation.Operator.EQ;
            case NE: return Operation.Operator.NE;
            case LT: return Operation.Operator.LT;
            case GE: return Operation.Operator.GE;
            case GT: return Operation.Operator.GT;
            case LE: return Operation.Operator.LE;
        }
        throw new IllegalArgumentException("convertOperator does not understand operator: " + operator);
    }

    private Expression convertCondition(SSAConditionalBranchInstruction cond) {
        return new Operation(
                convertOperator((IConditionalBranchInstruction.Operator)cond.getOperator()),
                new WalaVarExpr(cond.getUse(0)),
                new WalaVarExpr(cond.getUse(1)));
    }

    // precondiion: terminus is the loop join.
    private Stmt conditionalBranch(SSACFG cfg, ISSABasicBlock currentBlock, ISSABasicBlock terminus)
            throws StaticRegionException {

        SSAInstruction ins = currentBlock.getLastInstruction();
        if (!(ins instanceof SSAConditionalBranchInstruction)) {
            throw new StaticRegionException("Expect conditional branch at end of 2-path attemptSubregion");
        }
        // Handle case where terminus is either 'if' or 'else' branch;
        Expression condExpr = convertCondition((SSAConditionalBranchInstruction)ins);
        ISSABasicBlock thenBlock = Util.getTakenSuccessor(cfg, currentBlock);
        ISSABasicBlock elseBlock = Util.getNotTakenSuccessor(cfg, currentBlock);

        Stmt thenStmt, elseStmt;
        currentCondition.addLast(new PhiCondition(PhiCondition.Branch.Then, condExpr));
        this.blockConditionMap.put(new PhiEdge(currentBlock, thenBlock), new ArrayList(currentCondition));
        if (thenBlock.getNumber() < terminus.getNumber()) {
            thenStmt = attemptSubregionRec(cfg, thenBlock, terminus);
        } else {
            thenStmt = SkipStmt.skip;
        }
        currentCondition.removeLast();

        currentCondition.addLast(new PhiCondition(PhiCondition.Branch.Else, condExpr));
        this.blockConditionMap.put(new PhiEdge(currentBlock, elseBlock), new ArrayList(currentCondition));
        if (elseBlock.getNumber() < terminus.getNumber()) {
            elseStmt = attemptSubregionRec(cfg, elseBlock, terminus);
        } else {
            elseStmt = SkipStmt.skip;
        }
        currentCondition.removeLast();

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
            ISSABasicBlock nextBlock = cfg.getNormalSuccessors(currentBlock).iterator().next();
            this.blockConditionMap.put(new PhiEdge(currentBlock, nextBlock), new ArrayList(currentCondition));

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

    /*
        walk through method, attempting to find conditional veritesting regions
     */
    private void createStructuredConditionalRegions(IR ir, ISSABasicBlock currentBlock,
                                                   ISSABasicBlock endingBlock,
                                                   HashMap<String, StaticRegion> veritestingRegions) throws StaticRegionException {

        SSACFG cfg = ir.getControlFlowGraph();
        // terminating conditions
        if (currentBlock == endingBlock) { return; }

        //visitedBlocks.add(currentBlock);

        if (isBranch(cfg, currentBlock)) {
            try {
                reset();
                FindStructuredBlockEndNode finder = new FindStructuredBlockEndNode(cfg, currentBlock, endingBlock);
                ISSABasicBlock terminus = finder.findMinConvergingNode();
                Stmt s = attemptConditionalSubregion(cfg, currentBlock, terminus);
                int endIns = ((IBytecodeMethod) (ir.getMethod())).getBytecodeIndex(terminus.getFirstInstructionIndex());
                veritestingRegions.put(CreateStaticRegions.constructRegionIdentifier(ir, currentBlock), new StaticRegion(s, ir, false, endIns));
                System.out.println("Subregion: " + System.lineSeparator() + PrettyPrintVisitor.print(s));

                createStructuredConditionalRegions(ir, terminus, endingBlock, veritestingRegions);
                return;
            } catch (StaticRegionException sre ) {
                System.out.println("Unable to create subregion");
            }
            catch (InvalidClassFileException exception){
                System.out.println("Unable to create subregion");
            }
        }
        for (ISSABasicBlock nextBlock: cfg.getNormalSuccessors(currentBlock)) {
            createStructuredConditionalRegions(ir, nextBlock, endingBlock, veritestingRegions);
        }
    }


    public void createStructuredConditionalRegions(HashMap<String, StaticRegion> veritestingRegions) throws StaticRegionException {
        SSACFG cfg = ir.getControlFlowGraph();
        createStructuredConditionalRegions(ir, cfg.entry(), cfg.exit(), veritestingRegions);
    }


    public void createStructuredMethodRegion(HashMap<String, StaticRegion> veritestingRegions) throws StaticRegionException {

        reset();
        SSACFG cfg = ir.getControlFlowGraph();
        try {
            Stmt s = attemptMethodSubregion(cfg, cfg.entry(), cfg.exit());
            System.out.println("Method" + System.lineSeparator() + PrettyPrintVisitor.print(s));
            SSAInstruction[] insns = ir.getInstructions();
            int endIns = ((IBytecodeMethod) (ir.getMethod())).getBytecodeIndex(insns[insns.length - 1].iindex);
            veritestingRegions.put(CreateStaticRegions.constructMethodIdentifier(cfg.entry()), new StaticRegion(s, ir, true, endIns));
        } catch (StaticRegionException sre) {
            System.out.println("Unable to create a method summary subregion for: " + cfg.getMethod().getName().toString());
        } catch (InvalidClassFileException e) {
            e.printStackTrace();
        }
    }
}
