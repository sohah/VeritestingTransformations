package gov.nasa.jpf.symbc.veritesting.RangerDiscovery;

import java.util.HashMap;
import java.util.List;

/**
 * This is the key that defines for each node, what is the expected status for repair/synthesis
 */
public class NodeRepairKey {
    HashMap<String, NodeStatus> nodesKey = new HashMap<>();

    public void setNodesKey(List<String> nodesName, NodeStatus status) {
        for (int i = 0; i < nodesName.size(); i++) {
            nodesKey.put(nodesName.get(i), status);
        }
    }

    public NodeStatus getStatus(String nodeName) {
        return nodesKey.get(nodeName);
    }


    public void setNodesKey(String nodeName, NodeStatus status) {
        nodesKey.put(nodeName, status);
    }

}
