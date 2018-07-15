package gov.nasa.jpf.symbc.veritesting.AstTransformation.CFGConversion;

import com.ibm.wala.ssa.*;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;

import java.util.*;

    /* MWW: Relatively simple traversal that aborts on non-local jumps *other than for early
       returns and exceptions*.  It attempts to find the minimal convergent node
       for all non-exceptional and non-early-return paths.

        It starts from a prescribed region with a minimal and maximal node.  If there is
        no non-early-return path and no erroneous cases (described below),
        it returns the maximal node.

        Exceptional cases:
            local loops (back edges between minLimit and maxLimit).
            early continues from outer loops: a back edge from a node earlier than the minimal
                convergent node.
            user-level breaks or gotos: jumps beyond maxLimit

        For exceptions, it throws a StaticRegionException.  Since this will be a relatively
        common case, I have pre-built the exception as a static object for performance.  It
        might be better to re-factor the code to avoid exceptions, but there are currently
        many cases, so I think it simplifies the code to use them.
     */


public class FindStructuredBlockEndNode {

    HashSet<ISSABasicBlock> visited = null;
    HashMap<ISSABasicBlock, Integer> refCount = null;
    PriorityQueue<ISSABasicBlock> remaining = null;
    ISSABasicBlock maxConvergedNode = null;
    ISSABasicBlock maxLimit = null;
    ISSABasicBlock minLimit = null;
    SSACFG cfg;

    // Amortize the cost of throwing the exception; much cheaper if it is static.
    public static StaticRegionException staticRegionException = new StaticRegionException("FindStructuredBlockEndNode: mal-formed region");

    public FindStructuredBlockEndNode(SSACFG cfg, ISSABasicBlock initial, ISSABasicBlock maxLimit) {
        visited = new HashSet<>();
        refCount = new HashMap<>();
        remaining = new PriorityQueue<>((ISSABasicBlock o1, ISSABasicBlock o2)->o1.getNumber()-o2.getNumber());
        // set maxLimit to the end of the function if it is not provided.
        this.maxLimit = (maxLimit != null) ? maxLimit : cfg.exit();
        this.minLimit = initial;
        this.cfg = cfg;
    }

    void checkRanges(ISSABasicBlock parent, ISSABasicBlock b) throws StaticRegionException {
        // abort on "internal loop" case
        if (b.getNumber() <= parent.getNumber()) {
            throw staticRegionException;
        }

        // handle "max out of bounds" case
        if (maxConvergedNode != null &&
                maxConvergedNode.getNumber() > maxLimit.getNumber()) {
            throw staticRegionException;
        }
    }

    void adjustMaxConvergedNode(ISSABasicBlock b) throws StaticRegionException {
        if (maxConvergedNode == null ||
            maxConvergedNode.getNumber() < b.getNumber()) {
            maxConvergedNode = b;
        }
    }

    void incrementRefcount(ISSABasicBlock b) {
        if (!refCount.containsKey(b)) {
            refCount.put(b, 1);
        } else {
            refCount.put(b, refCount.get(b)+1);
        }
    }

    // idea: add element
    void enqueue(ISSABasicBlock elem) {
        if (!remaining.contains(elem)) {
            remaining.add(elem);
        }
    }

    void findCommonSuccessor(ISSABasicBlock b) throws StaticRegionException {

        for (ISSABasicBlock succ: cfg.getNormalSuccessors(b)) {
            checkRanges(b, succ);
            enqueue(succ);
        }

        // Size of the queue is the number of open paths in the model.
        while (remaining.size() > 1) {
            ISSABasicBlock current = remaining.poll();
            SSAInstruction last = current.getLastInstruction();
            // We do not want to continue to explore successors of blocks ending with
            // returns or exceptions.
            if (!(last instanceof SSAReturnInstruction) && !(last instanceof SSAThrowInstruction)) {
                for (ISSABasicBlock succ : cfg.getNormalSuccessors(current)) {
                    checkRanges(current, succ);
                    enqueue(succ);
                }
            }
        }

        maxConvergedNode = remaining.poll();
    }

    public ISSABasicBlock findMinConvergingNode() throws StaticRegionException {

        // we have already computed it.
        if (maxConvergedNode != null) {
           return maxConvergedNode;
        }

        List<ISSABasicBlock> succs = new ArrayList<>(cfg.getNormalSuccessors(minLimit));
        if (succs.size() == 0) {
            throw staticRegionException;
        }
        else if (succs.size() == 1) {
            return succs.get(0);
        }
        else {
            findCommonSuccessor(minLimit);
            return maxConvergedNode;
        }
    }
}
