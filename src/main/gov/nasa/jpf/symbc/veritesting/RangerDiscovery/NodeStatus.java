package gov.nasa.jpf.symbc.veritesting.RangerDiscovery;

/**
 * This is used to identify the nodes that we need to repair and those that we just need to add without repair, and finally those that are added by the tool but not really part of the specification.
 */
public enum NodeStatus {
REPAIR, DONTCARE_SPEC, ARTIFICIAL
}
