package gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst;

import com.ibm.wala.cfg.Util;
import com.ibm.wala.classLoader.IBytecodeMethod;
import com.ibm.wala.shrikeCT.InvalidClassFileException;
import com.ibm.wala.ssa.*;
import com.ibm.wala.util.graph.Graph;
import com.ibm.wala.util.graph.dominators.Dominators;
import com.ibm.wala.util.graph.dominators.NumberedDominators;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.SSAToStatIVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.PrettyPrintVisitor;
import za.ac.sun.cs.green.expr.*;

import java.util.*;

/*
    This class creates our structure IR from the WALA SSA form for further transformation.

    TODO: In examining the debug output, it appears that the same classes and methods are visited multiple times.  Why?

    Here we are essentially decompiling DAGs within a Java program.  The goals
    are two-fold:
        1. It should be accurate.  Any semantics violating decompilation steps
            will obviously cause SPF to misbehave
        2. It should be lightweight.  Any fixpoint algorithms may cost a lot
            in preprocessing.

    It does *not* need to be complete.  It is o.k. if 'continue's and 'break's
    cause the generation algorithm to fail; we will skip those regions.  As
    long as we aren't analyzing malware, this won't happen too often.

    * One tricky bit involves figuring out the boundaries of complex 'if' conditions.

    It is not too bad; you look for "immediate self-contained subgraphs", that is,
    subgraphs where the initial node is immediately pre-dominated by the initial node
    and for the static region and whose successor nodes (up to the region terminus) are
    dominated (not necessarily immediately) by the initial node.

    For the things we want to analyze, there should be one (for if-no-else) or
    two (for if-else) of these regions.

    For if-no-else regions, it is clear what to use as the 'then' condition, but
    with if-else regions, it is not so clear.  We use the initial condition
    'then' branch to choose, but this is pretty arbitrary, and in fact WALA seems
    to reverse the if/else branches from the source code.  This is probably because
    the jump conditions are 'jump zero'.

    We create a successor map that jumps directly to these 'then' and 'else'
    elements, and generate the condition for the 'then' branch.  Thereafter, we
    can view the problem as one of nested self-contained subgraphs, which
    simplifies the rest of the region processing.


    * Another tricky bit involves translating \phi instructions to \gammas.

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

    private IR ir;
    private Graph<ISSABasicBlock> domTree;

    // For Phi instructions.  See comment at top of file
    private Map<PhiEdge, List<PhiCondition>> blockConditionMap;
    private Deque<PhiCondition> currentCondition;

    // for complex conditions, we want to record the then condition and successors.
    // See the comment at the top of the file for more information.
    private Map<ISSABasicBlock, Expression> thenCondition;
    private Map<ISSABasicBlock, ISSABasicBlock> thenSuccessor;
    private Map<ISSABasicBlock, ISSABasicBlock> elseSuccessor;

    // For memoization, so we don't visit the same blocks over and over.
    private Set<ISSABasicBlock> visitedBlocks;
    // TODO: an optimization to be explored for future is to subclass the HashMap type
    // TODO: so we store *unsuccessful* regions.  This would allow us to do region
    // TODO: construction "on the fly" without revisiting unsuccessful regions multiple times.

    public CreateStaticRegions(IR ir) {
        blockConditionMap = new HashMap<>();
        currentCondition = new LinkedList<>();
        thenCondition = new HashMap<>();
        thenSuccessor = new HashMap<>();
        elseSuccessor = new HashMap<>();
        visitedBlocks = new HashSet<>();

        this.ir = ir;

        /* MWW: added to determine complex conditions */
        SSACFG cfg = ir.getControlFlowGraph();
        NumberedDominators<ISSABasicBlock> dom = (NumberedDominators) Dominators.make(cfg, cfg.entry());
        this.domTree = dom.dominatorTree();
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


    private ISSABasicBlock getIDom(ISSABasicBlock elem) {
        assert(this.domTree.getPredNodeCount(elem) == 1);
        return (ISSABasicBlock)this.domTree.getPredNodes(elem).next();
    }


    // This method checks to see whether each node in a subgraph up to a
    // terminus (see comment at top of file)
    private boolean isSelfContainedSubgraph(ISSABasicBlock entry, ISSABasicBlock terminus) throws StaticRegionException {
        // trivial case.
        if (entry == terminus) { return false; }

        SSACFG cfg = ir.getControlFlowGraph();
        PriorityQueue<ISSABasicBlock> toVisit = SSAUtil.constructSortedBlockPQ();
        Set<ISSABasicBlock> visited = new HashSet<>();

        visited.add(entry);
        toVisit.addAll(SSAUtil.getNonReturnSuccessors(cfg, entry));

        while (!toVisit.isEmpty()) {
            ISSABasicBlock current = toVisit.remove();
            if (!visited.contains(current)) {
                visited.add(current);
                ISSABasicBlock immediatePreDom = getIDom(current);
                if (current == terminus) {
                    // because of priority queue, a non-empty queue means we have
                    // successor nodes beyond the terminus node, so error out.
                    if (!toVisit.isEmpty()) {
                        throw new StaticRegionException("isSelfContainedSubgraph: non-empty queue at return");
                    }
                    return true;
                } else if (!visited.contains(immediatePreDom)) {
                    // not self contained!
                    return false;
                } else {
                    SSAUtil.getNonReturnSuccessors(cfg, current).forEach(
                            succ -> SSAUtil.enqueue(toVisit, succ));
                }
            }
        }
        // This condition occurs when we have a region terminated by a 'return'
        // We treat these as self-contained.
        return true;
    }

    private void findSelfContainedSubgraphs(ISSABasicBlock entry,
                                   ISSABasicBlock current,
                                   ISSABasicBlock terminus,
                                   Set<ISSABasicBlock> subgraphs) throws StaticRegionException {

        if (subgraphs.contains(current) || current == terminus) {  return; }

        if (isSelfContainedSubgraph(current, terminus)) {
            subgraphs.add(current);
        } else {
            // in 'else' because we want only the earliest self-contained subgraphs
            for (ISSABasicBlock succ : ir.getControlFlowGraph().getNormalSuccessors(current)) {
                findSelfContainedSubgraphs(entry, succ, terminus, subgraphs);
            }
        }
    }

    /*
        Re-constructs a complex condition for an if/then/else condition.

        MWW: I make several assumptions here about the structure of the nodes between
            currentBlock and entry; if they are violated then I have misunderstood something
            about the structure of the region, so I throw a 'severe' exception.

        If there are stateful operations in the if/then/else, then the internal
        conditions will have >1 statement.  For now we will abort with a SRE, but
        we could hoist them out in some cases.

        MWW TODO: Do we wish to allow stateful conditions in ITEs?
           TODO: We would have to hoist operations; a little bit
           TODO: tricky, so I am not going to bother with it now.
     */

    private Expression createComplexIfCondition(ISSABasicBlock child,
                                                ISSABasicBlock entry) throws StaticRegionException {
        assert(child.getNumber() > entry.getNumber());
        SSACFG cfg = ir.getControlFlowGraph();
        Expression returnExpr = null;

        for (ISSABasicBlock parent: cfg.getNormalPredecessors(child)) {
            if (!SSAUtil.isConditionalBranch(parent)) {
                throw new StaticRegionException("createComplexIfCondition: unconditional branch (continue or break)");
            }
            else if (parent != entry && SSAUtil.statefulBlock(parent)) {
                throw new StaticRegionException("createComplexIfCondition: stateful condition");
            }

            assert(child == Util.getTakenSuccessor(cfg, parent) ||
                   child == Util.getNotTakenSuccessor(cfg, parent));

            Expression branchExpr;
            Expression condExpr = SSAUtil.convertCondition(ir, SSAUtil.getLastBranchInstruction(parent));
            if (child == Util.getNotTakenSuccessor(cfg, parent)) {
                condExpr = new Operation(Operation.Operator.NOT, condExpr);
            }

            if (parent == entry) {
                branchExpr = condExpr;
            }
            else {
                Expression parentExpr = createComplexIfCondition(parent, entry);
                branchExpr = new Operation(Operation.Operator.AND, parentExpr, condExpr);
            }

            if (returnExpr == null) {
                returnExpr = branchExpr;
            } else {
                returnExpr = new Operation(Operation.Operator.OR, returnExpr, branchExpr);
            }
        }
        assert(returnExpr != null);
        return returnExpr;
    }

    /*
        // MWW: debugging
        System.out.println("For entry: " + entry);
        for (ISSABasicBlock starter: subgraphs) {
            System.out.println("   Subgraph: " + starter);
        }
        // MWW: end of debugging.
     */
    private void findConditionalSuccessors(ISSABasicBlock entry,
                                           ISSABasicBlock terminus) throws StaticRegionException {

        Set<ISSABasicBlock> subgraphs = new HashSet<>();
        SSACFG cfg = ir.getControlFlowGraph();
        ISSABasicBlock initialThenBlock = Util.getTakenSuccessor(cfg, entry);
        ISSABasicBlock initialElseBlock = Util.getNotTakenSuccessor(cfg, entry);
        ISSABasicBlock thenBlock, elseBlock;

        findSelfContainedSubgraphs(entry, initialThenBlock, terminus, subgraphs);
        findSelfContainedSubgraphs(entry, initialElseBlock, terminus, subgraphs);

        // if (no-else) region
        if (subgraphs.size() == 1) {
            thenBlock = subgraphs.iterator().next();
            elseBlock = terminus;
        }
        // if/else region; choice of 'thenBlock' is arbitrary.
        else if (subgraphs.size() == 2) {
            Iterator<ISSABasicBlock> it = subgraphs.iterator();
            thenBlock = it.next();
            elseBlock = it.next();
        }
        else {
            // MWW: I don't anticipate this condition ever occurring, but it might;
            // esp. for JVM programs not compiled by Java compiler.
            String errorText = "Unexpected number (" + subgraphs.size() +
                    ") of self-contained regions in findConditionalSuccessors";
            System.out.println(errorText);
            throw new StaticRegionException(errorText);
        }
        this.thenSuccessor.put(entry, thenBlock);
        this.elseSuccessor.put(entry, elseBlock);
        Expression cond = createComplexIfCondition(thenBlock, entry);
        this.thenCondition.put(entry, cond);
    }

    // precondition: terminus is the loop join.
    private Stmt conditionalBranch(SSACFG cfg, ISSABasicBlock currentBlock, ISSABasicBlock terminus)
            throws StaticRegionException {

        if (!SSAUtil.isConditionalBranch(currentBlock)) {
            throw new StaticRegionException("conditionalBranch: no conditional branch!");
        }

        findConditionalSuccessors(currentBlock, terminus);
        Expression condExpr = thenCondition.get(currentBlock);
        ISSABasicBlock thenBlock = thenSuccessor.get(currentBlock);
        ISSABasicBlock elseBlock = elseSuccessor.get(currentBlock);

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

        return new IfThenElseStmt(SSAUtil.getLastBranchInstruction(currentBlock), condExpr, thenStmt, elseStmt);
    }

    /*
        This method translates from currentBlock up to but not including endingBlock.
        Doing it this way makes it much simpler to deal with nested if/then/elses that land in the same spot.

        It also makes it simpler to tailor the end of the translation: for methods, we want to grab the
        remaining code within the method, while for conditional blocks we only want to grab the subsequent \phi
        functions.

        NB: same block may be visited multiple times!
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
    private void createStructuredConditionalRegions(ISSABasicBlock currentBlock,
                                                   ISSABasicBlock endingBlock,
                                                   HashMap<String, StaticRegion> veritestingRegions) throws StaticRegionException {

        if (visitedBlocks.contains(currentBlock)) { return; }
        visitedBlocks.add(currentBlock);

        SSACFG cfg = ir.getControlFlowGraph();
        // terminating conditions
        if (currentBlock == endingBlock) { return; }


        if (isBranch(cfg, currentBlock)) {
            try {
                reset();
                FindStructuredBlockEndNode finder = new FindStructuredBlockEndNode(cfg, currentBlock, endingBlock);
                ISSABasicBlock terminus = finder.findMinConvergingNode();
                Stmt s = attemptConditionalSubregion(cfg, currentBlock, terminus);
                int endIns = ((IBytecodeMethod) (ir.getMethod())).getBytecodeIndex(terminus.getFirstInstructionIndex());
                veritestingRegions.put(CreateStaticRegions.constructRegionIdentifier(ir, currentBlock), new StaticRegion(s, ir, false, endIns));
                System.out.println("Subregion: " + System.lineSeparator() + PrettyPrintVisitor.print(s));

                createStructuredConditionalRegions(terminus, endingBlock, veritestingRegions);
                return;
            } catch (StaticRegionException e ) {
                //SSAUtil.printBlocksUpTo(cfg, endingBlock.getNumber());
                System.out.println("Unable to create subregion.  Reason: " + e.toString());
            } catch (InvalidClassFileException e){
                System.out.println("Unable to create subregion.  Reason: " + e.toString());
            } catch (IllegalArgumentException e) {
                System.out.println("Unable to create subregion.  Serious error. Reason: " + e.toString());
                throw e;
            }
        }
        for (ISSABasicBlock nextBlock: cfg.getNormalSuccessors(currentBlock)) {
            createStructuredConditionalRegions(nextBlock, endingBlock, veritestingRegions);
        }
    }


    public void createStructuredConditionalRegions(HashMap<String, StaticRegion> veritestingRegions) throws StaticRegionException {
        SSACFG cfg = ir.getControlFlowGraph();
        // SSAUtil.printBlocksUpTo(cfg, cfg.exit().getNumber());
        createStructuredConditionalRegions(cfg.entry(), cfg.exit(), veritestingRegions);
    }


    public void createStructuredMethodRegion(HashMap<String, StaticRegion> veritestingRegions) throws StaticRegionException {

        reset();
        SSACFG cfg = ir.getControlFlowGraph();
        try {
            Stmt s = attemptMethodSubregion(cfg, cfg.entry(), cfg.exit());
            System.out.println("Method" + System.lineSeparator() + PrettyPrintVisitor.print(s));
            SSAInstruction[] insns = ir.getInstructions();
            //int endIns = ((IBytecodeMethod) (ir.getMethod())).getBytecodeIndex(insns[insns.length - 1].iindex);
            veritestingRegions.put(CreateStaticRegions.constructMethodIdentifier(cfg.entry()), new StaticRegion(s, ir, true, 0));
        } catch (StaticRegionException sre) {
            System.out.println("Unable to create a method summary subregion for: " + cfg.getMethod().getName().toString());
        }
    }
}
