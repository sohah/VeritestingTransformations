package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.LustreExtension;

import jkind.lustre.*;
import jkind.lustre.visitors.AstMapVisitor;

import java.util.List;

//removes the repair expression and keeps the initial value of the suggested repair.
public class RemoveRepairConstructVisitor extends AstMapVisitor {

    @Override
    public Program visit(Program e) {
        List<TypeDef> types = visitTypeDefs(e.types);
        List<Constant> constants = visitConstants(e.constants);
        List<Function> functions = visitFunctions(e.functions);
        List<Node> nodes = visitNodes(e.nodes);
        return new Program(e.location, types, constants, functions, nodes, null, e.main);
    }


    @Override
    public Expr visit(RepairExpr e) {
        if (e.origExpr instanceof RepairExpr){
            System.out.println("default original expression cannot be of type RepairExpr! Aborting");
            assert false;
        }
        return e.origExpr.accept(this);
    }


    public static Program execute(Program originalPgm){
        RemoveRepairConstructVisitor removeRepairConstructVisitor = new RemoveRepairConstructVisitor();
        return removeRepairConstructVisitor.visit(originalPgm);
    }
}
