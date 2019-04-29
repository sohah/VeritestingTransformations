package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.MinimalRepair;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Contract;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil;
import jkind.lustre.*;

import java.util.ArrayList;
import java.util.List;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config.*;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil.addProperty;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil.removeNodeStr;

public class MinimalRepairCheck {

    //used to identify the new free variables, that are going to be exactly like the locals defined in the main, so we have to distinguish them with some unique names
    public static final String internalId = "__";


    public static Program execute(Contract contract, Program origCounterEx, Node fixedTNode, Node candTnode) {

        //Node tNode = addProperty("p1", DiscoveryUtil.renameNode(TNODE, fixedTNode)); //rename it to R so we can call
        // it again

        Node tNode = DiscoveryUtil.renameNode(TNODE, fixedTNode); //rename it to R so we can call it again

        Node tPrimeNode = DiscoveryUtil.renameNode(CAND_T_PRIME, candTnode); //rename it to R so we can call it again

        List<Node> newNodes = new ArrayList<>(origCounterEx.nodes);


        newNodes = removeNodeStr(newNodes, origCounterEx.main);

        newNodes = removeNodeStr(newNodes, TNODE);

        newNodes.add(tNode);
        newNodes.add(tPrimeNode);

        Node mainNode = generateMainNode(origCounterEx.getMainNode());

        newNodes.add(mainNode);
        return new Program(origCounterEx.location, origCounterEx.types, origCounterEx.constants, origCounterEx.functions, newNodes, null, origCounterEx.main);

    }

    private static Node generateMainNode(Node mainNode) {

        List<VarDecl> oldInputVars = mainNode.inputs;
        List<VarDecl> oldLocals = mainNode.locals;
        List<Equation> oldEq = mainNode.equations;

        assert oldEq.size() == 2;
        Equation oldWrapperEq = oldEq.get(0);
        assert oldWrapperEq.toString().contains("wrapper");

        Equation oldT_nodeCallEq = oldEq.get(1);
        assert oldT_nodeCallEq.toString().contains("T_node");


        List<VarDecl> newFreeOutVarDecls = createNewFreeOutVars(mainNode);
        List<IdExpr> newFreeOutExprs = DiscoveryUtil.varDeclToIdExpr(newFreeOutVarDecls);

        List<VarDecl> newInputs = new ArrayList(oldInputVars);
        newInputs.addAll(newFreeOutVarDecls);


        VarDecl isMatchImpVarDecl = new VarDecl("isMatchImpl", NamedType.BOOL);
        VarDecl isTighterVarDecl = new VarDecl("isTighter", NamedType.BOOL);
        List<VarDecl> newLocals = new ArrayList(oldLocals);
        newLocals.add(isMatchImpVarDecl);
        newLocals.add(isTighterVarDecl);


        IdExpr isMatchImplExpr = DiscoveryUtil.varDeclToIdExpr(isMatchImpVarDecl);
        IdExpr isTighterExpr = DiscoveryUtil.varDeclToIdExpr(isTighterVarDecl);


        Equation newDiscoveryOut = new Equation(oldT_nodeCallEq.lhs, new BinaryExpr(isMatchImplExpr, BinaryOp.AND, isTighterExpr));

        Equation isMatchImpEq = new Equation(isMatchImplExpr, new NodeCallExpr(CAND_T_PRIME, ((NodeCallExpr)
                oldT_nodeCallEq.expr).args));

        List<Expr> tighterCallParams = new ArrayList<>(DiscoveryUtil.varDeclToIdExpr(oldInputVars));
        tighterCallParams.addAll(newFreeOutExprs);

        Expr tPrimeTightCall = new NodeCallExpr(CAND_T_PRIME, tighterCallParams);

        Expr tFixedtightCall = new NodeCallExpr(TNODE, tighterCallParams);

        Equation tighterEq = new Equation(isTighterExpr, new BinaryExpr(tPrimeTightCall, BinaryOp.IMPLIES, tFixedtightCall));

        List<Equation> newEquations = new ArrayList<Equation>();
        newEquations.add(oldWrapperEq);
        newEquations.add(isMatchImpEq);
        newEquations.add(tighterEq);
        newEquations.add(newDiscoveryOut);

        List<String> newProperties = new ArrayList<>();
        newProperties.add(Config.candidateSpecPropertyName);

        return new Node("main", newInputs, mainNode.outputs, newLocals, newEquations, newProperties, mainNode.assertions, mainNode.realizabilityInputs, mainNode.contract, mainNode.ivc);
    }

    private static List<VarDecl> createNewFreeOutVars(Node mainNode) {

        List<VarDecl> newFree = new ArrayList<>();

        for (VarDecl e : mainNode.locals) {
            newFree.add(new VarDecl(e.id + internalId, e.type));
        }
        return newFree;
    }
}
