package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DefSpecRepair;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DefSpecRepair.repairbuilders.CandidateRepairExpr;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DefSpecRepair.repairbuilders.FaultyEquation;
import jkind.lustre.*;

import java.util.List;

public class SubstitutionVisitor {
    public static Program substitute(Program pgmT, CandidateRepairExpr candidateRepairExpr, FaultyEquation faultyEquation) {
        List<TypeDef> types = pgmT.types;
        List<Constant> constants = pgmT.constants;
        List<Function> functions = pgmT.functions;
        List<Node> nodes = pgmT.nodes;
        String main = pgmT.main;


        //Program
        return null;

    }
}
