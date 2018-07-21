package gov.nasa.jpf.symbc.veritesting.ast.transformations.phiToGamma;

/*
Vaibhav: This class' main purpose is, given a CFG, branching node, and a terminus node that begins with a Phi
instruction, put the Phi's uses in taken/not-taken order based on the branch.
*/

import com.ibm.wala.ssa.ISSABasicBlock;
import com.ibm.wala.ssa.SSACFG;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

public class DerivePhiOrder {
    public static int getPhiUseNumIndex(SSACFG cfg, ISSABasicBlock start, ISSABasicBlock terminus) {
        Iterator<ISSABasicBlock> predNodesItr = cfg.getPredNodes(terminus);
        List predNodes = new ArrayList<ISSABasicBlock>();
        while (predNodesItr.hasNext()) { predNodes.add(predNodesItr.next()); }
        int pos = dfs(cfg, start, predNodes, terminus);
        return pos;
    }

    private static int dfs(SSACFG cfg, ISSABasicBlock node, List predNodes, ISSABasicBlock terminus) {
        if (predNodes.contains(node)) return predNodes.indexOf(node);
        List<ISSABasicBlock> succNodes = new ArrayList<>();
        Iterator<ISSABasicBlock> itr = cfg.getSuccNodes(node);
        while(itr.hasNext()) {
            ISSABasicBlock succ = itr.next();
            // The 2nd condition should never happen but I (Vaibhav) am being defensive
            if (succ.getNumber() > terminus.getNumber() || succ.getNumber() < node.getNumber()) continue;
            succNodes.add(succ);
        }

        if (succNodes.size() != 1) return -1;
        return dfs(cfg, succNodes.get(0), predNodes, terminus);
    }
}
