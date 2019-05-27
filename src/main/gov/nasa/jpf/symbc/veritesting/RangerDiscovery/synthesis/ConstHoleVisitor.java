package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.synthesis;

import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import jkind.lustre.Node;
import jkind.lustre.VarDecl;
import jkind.lustre.visitors.AstMapVisitor;

import java.util.ArrayList;
import java.util.List;

public class HoleVisitor extends AstMapVisitor{
    private List<VarDecl> holeVarDecl = new ArrayList<>();
    private static List<Node> beforeNodes = new ArrayList<>();
    private static List<Node> holeNodes = new ArrayList<>();



    public Pair<Node, List<VarDecl>> execute(List<Node> beforeNodes){


    }



}
