package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.MinimalRepair;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil;
import jkind.lustre.Node;
import jkind.lustre.Program;

import java.util.ArrayList;
import java.util.List;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config.CAND_T_PRIME;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config.TNODE;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil.removeNodeStr;

public class MinimalRepairCheck {

    public static Program execute(Program origCounterEx, Node fixedTNode, Node candTnode) {

        Node rNode = DiscoveryUtil.renameNode(TNODE, fixedTNode); //rename it to R so we can call it again

        Node rPrimeNode = DiscoveryUtil.renameNode(CAND_T_PRIME, candTnode); //rename it to R so we can call it again

        List<Node> newNodes = new ArrayList<>(origCounterEx.nodes);


        newNodes = removeNodeStr(newNodes, origCounterEx.main);

        newNodes = removeNodeStr(newNodes, TNODE);

        newNodes.add(rNode);
        newNodes.add(rPrimeNode);

        Node mainNode = generateMainNode(origCounterEx.getMainNode());

        newNodes.add(mainNode);
        return new Program(origCounterEx.location, origCounterEx.types, origCounterEx.constants, origCounterEx.functions, newNodes, null, origCounterEx.main);

    }

    private static Node generateMainNode(Node mainNode) {

        return null;
    }
}
