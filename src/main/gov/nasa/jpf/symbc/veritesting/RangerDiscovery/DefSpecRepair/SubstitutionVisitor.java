package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DefSpecRepair;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DefSpecRepair.repairbuilders.CandidateRepairExpr;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DefSpecRepair.repairbuilders.FaultyEquation;
import jkind.lustre.*;

import java.util.ArrayList;
import java.util.List;

public class SubstitutionVisitor {
    public static Program substitute(Program pgmT, CandidateRepairExpr candidateRepairExpr, FaultyEquation faultyEquation) {
        List<Node> nodes = substituteInNode(pgmT.nodes, candidateRepairExpr, faultyEquation);

        //Program
        return new Program(pgmT.location, pgmT.types, pgmT.constants, pgmT.functions, nodes, null, pgmT.main);

    }

    private static List<Node> substituteInNode(List<Node> nodes, CandidateRepairExpr candidateRepairExpr, FaultyEquation faultyEquation) {
        List<Node> newNodes = new ArrayList<>();

        for (int i = 0; i < nodes.size(); i++) {
            if (nodes.get(i).id.equals(faultyEquation.node.id))
                newNodes.add(substituteInEquations(nodes.get(i), candidateRepairExpr, faultyEquation));
            else
                newNodes.add(nodes.get(i));
        }
        return newNodes;
    }

    private static Node substituteInEquations(Node node, CandidateRepairExpr candidateRepairExpr, FaultyEquation faultyEquation) {
        List<Equation> equations = node.equations;
        List<Equation> newEquations = new ArrayList<>();

        for (int i = 0; i < equations.size(); i++) {
            if (equations.get(i).lhs.get(0).id.equals(faultyEquation.def.id))
                newEquations.add(new Equation(equations.get(i).lhs, candidateRepairExpr.expr));
            else
                newEquations.add(equations.get(i));
        }
        List<VarDecl> newInputs = new ArrayList<>(node.inputs);
        newInputs.addAll(new ArrayList<>(candidateRepairExpr.getHoleMap().values()));
        return new Node(node.id, newInputs, node.outputs, node.locals, newEquations, node.properties, node.assertions, node.realizabilityInputs, node.contract, node.ivc);
    }
}
