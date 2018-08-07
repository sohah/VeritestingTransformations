package gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment;

import com.ibm.wala.shrikeBT.IBinaryOpInstruction;
import com.ibm.wala.shrikeBT.IComparisonInstruction;
import com.ibm.wala.shrikeBT.IUnaryOpInstruction;
import com.ibm.wala.ssa.*;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.PhiCondition;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.PhiEdge;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.SSAUtil;
import za.ac.sun.cs.green.expr.*;

import java.util.*;


//SH: This class translates SSAInstructions to Veritesting Statements.


public class SSAToStatIVisitor implements SSAInstruction.IVisitor {
    public Stmt veriStatement;
    public boolean canVeritest = true;

    private IR ir;
    private Map<PhiEdge, List<PhiCondition>> blockConditionMap;
    private Deque<PhiCondition> currentCondition;
    private ISSABasicBlock currentBlock;
    private StaticRegionException pending = null;

    public SSAToStatIVisitor(IR ir,
                             ISSABasicBlock currentBlock,
                             Map<PhiEdge, List<PhiCondition>> blockConditionMap,
                             Deque<PhiCondition> currentCondition) {
        this.ir = ir;
        this.currentBlock = currentBlock;
        this.blockConditionMap = blockConditionMap;
        this.currentCondition = currentCondition;

    }

/*
    Beginning of methods for translating Phi instructions...
 */

/*
        If we want to convert constants to values eagerly, we can add this code back in.
        However, I don't think it is necessary.

       SymbolTable symtab = ir.getSymbolTable();

        if (symtab.isConstant(ssaVar)) {
            Object val = symtab.getConstantValue(ssaVar);
            if (val instanceof Boolean) {
                return new IntConstant(val.equals(Boolean.TRUE) ? 1 : 0);
            } else if (val instanceof Integer) {
                return new IntConstant((Integer)val);
            } else if (val instanceof Double) {
                return new RealConstant((Double)val);
            } else if (val instanceof String) {
                return new StringConstantGreen((String)val);
            } else {
                throw new StaticRegionException("translateTruncatedFinalBlock: unsupported constant type");
            }
        } else {
*/

    private Expression convertWalaVar(int ssaVar) {
        SymbolTable symtab = ir.getSymbolTable();
        if (symtab.isConstant(ssaVar)) {
            Object val = symtab.getConstantValue(ssaVar);
            if (val instanceof Boolean) {
                return new IntConstant(val.equals(Boolean.TRUE) ? 1 : 0);
            } else if (val instanceof Integer) {
                return new IntConstant((Integer)val);
            } else if (val instanceof Double) {
                return new RealConstant((Double)val);
            } else if (val instanceof String) {
                return new StringConstantGreen((String)val);
            } else {
                throw new IllegalArgumentException("translateTruncatedFinalBlock: unsupported constant type");
            }
        } else {
            return new WalaVarExpr(ssaVar);
        }
    }


    private Expression conjunct(List<Expression> le) {
        if (le.size() == 0) {
            return Operation.TRUE;
        }
        Expression result = le.get(0);
        for (int i = 1; i < le.size(); i++) {
            result = new Operation(Operation.Operator.AND, result, le.get(i));
        }
        return result;
    }

    private Expression getAndCheckCondition(List<LinkedList<PhiCondition>> conds) {
        Expression cond = conds.get(0).getFirst().condition;
        for (int i = 1; i < conds.size(); i++) {
            if (conds.get(i).getFirst().condition != cond) {
                throw new IllegalArgumentException("Error in getAndCheckCondition: conditions did not match!!!");
            }
        }
        return cond;
    }

    private Expression createGamma(List<LinkedList<PhiCondition>> conds, List<Expression> values) throws StaticRegionException {

        //assert(!conds.isEmpty());
        if(conds.isEmpty())
            throw sre;

        // Handle leaf-level assignment
        if (conds.get(0).isEmpty()) {
            assert (conds.size() == 1);
            return values.get(0);
        }

        // Handle if/then:
        // Separate 'then' and 'else' branches.
        List<LinkedList<PhiCondition>> thenConds = new ArrayList<>();
        List<LinkedList<PhiCondition>> elseConds = new ArrayList<>();
        List<Expression> thenValues = new ArrayList<>();
        List<Expression> elseValues = new ArrayList<>();

        Expression cond = getAndCheckCondition(conds);

        // NB: this code modifies the linked list as it runs.
        for (int i = 0; i < conds.size(); i++) {
            LinkedList<PhiCondition> phiConditions = conds.get(i);
            PhiCondition first = phiConditions.removeFirst();
            if (first.branch == PhiCondition.Branch.Then) {
                thenConds.add(phiConditions);
                thenValues.add(values.get(i));
            } else {
                elseConds.add(phiConditions);
                elseValues.add(values.get(i));
            }
        }

        return new GammaVarExpr(cond,
                createGamma(thenConds, thenValues),
                createGamma(elseConds, elseValues));
    }

    // If this phi is for a nested if/then/else, ignore the "out of scope"
    // conditions corresponding to ancestor branches.
    public void adjustForDepth(List<LinkedList<PhiCondition>> conds) {
        int depth = this.currentCondition.size();
        for (LinkedList<PhiCondition> cond : conds) {
            for (int j=0; j < depth; j++) {
                cond.removeFirst();
            }
        }
    }

    public Stmt translatePhi(SSAPhiInstruction ssaphi) throws StaticRegionException {
        SSACFG cfg = ir.getControlFlowGraph();
        SymbolTable symtab = ir.getSymbolTable();
        Collection<ISSABasicBlock> preds = cfg.getNormalPredecessors(currentBlock);
        Iterator<ISSABasicBlock> it = preds.iterator();
        if (ssaphi.getNumberOfUses() != preds.size()) {
            throw new StaticRegionException("translateTruncatedFinalBlock: normal predecessors size does not match number of phi branches");
        }
        else {
            List<LinkedList<PhiCondition>> conds = new ArrayList<LinkedList<PhiCondition>>();
            List<Expression> values = new ArrayList<>();

            for (int i = 0; i < ssaphi.getNumberOfUses(); i++) {
                int ssaVar = ssaphi.getUse(i);
                ISSABasicBlock preBlock = it.next();

                List<PhiCondition> cond = blockConditionMap.get(new PhiEdge(preBlock, currentBlock));
                if (cond == null) {
                    System.out.println("Unable to find condition.");
                    SSAUtil.printBlocksUpTo(cfg, currentBlock.getNumber());
                    // MWW: null case.  Do not add to the gamma.
                    // MWW: This case occurs due to jumps from complex 'if' conditions.
                    // MWW: the top one of them will be in the blockConditionMap, but subsequent ones
                    // MWW: will not be placed in the map.
                }
                else {
                    conds.add(new LinkedList<PhiCondition>(cond));
                    values.add(convertWalaVar(ssaVar));
                }
            }
            // create Gamma statement
            adjustForDepth(conds);
            return new AssignmentStmt(new WalaVarExpr(ssaphi.getDef()), createGamma(conds, values));
        }
    }

    /*
        End of Phi translating methods.
     */

    @Override
    public void visitGoto(SSAGotoInstruction ssaGotoInstruction) {
        throw new IllegalArgumentException("Goto seen in SSAToStatIVisitor.  This should not occur.");
    }

    @Override
    public void visitArrayLoad(SSAArrayLoadInstruction ssaArrayLoadInstruction) {
        veriStatement = new gov.nasa.jpf.symbc.veritesting.ast.def.ArrayLoadInstruction(ssaArrayLoadInstruction);
    }

    @Override
    public void visitArrayStore(SSAArrayStoreInstruction ssaArrayStoreInstruction) {
        veriStatement = new gov.nasa.jpf.symbc.veritesting.ast.def.ArrayStoreInstruction(ssaArrayStoreInstruction);
    }

    private Operation.Operator translateBinaryOp(IBinaryOpInstruction.Operator op) {
        switch (op) {
            case ADD: return Operation.Operator.ADD;
            case SUB: return Operation.Operator.SUB;
            case MUL: return Operation.Operator.MUL;
            case DIV: return Operation.Operator.DIV;
            case REM: return Operation.Operator.MOD;
            case AND: return Operation.Operator.AND;
            case OR: return Operation.Operator.OR;
            case XOR: return Operation.Operator.NOTEQUALS;
        }
        throw new IllegalArgumentException("Unknown Operator: " + op.toString() + " in translateBinaryOp");
    }

    @Override
    public void visitBinaryOp(SSABinaryOpInstruction ssa) {
        Expression lhs = new WalaVarExpr(ssa.getDef());
        Operation.Operator op = translateBinaryOp((IBinaryOpInstruction.Operator)ssa.getOperator());
        Expression op1 = convertWalaVar(ssa.getUse(0));
        Expression op2 = convertWalaVar(ssa.getUse(1));
        Expression rhs = new Operation(op, op1, op2);
        Stmt s = new AssignmentStmt(lhs, rhs);
        veriStatement = s;
        /*veriStatement = new AssignmentStmt(new WalaVarExpr(ssa.getDef()),
                new Operation(
                        translateBinaryOp((IBinaryOpInstruction.Operator)ssa.getOperator()),
                        new WalaVarExpr(ssa.getUse(0)),
                        new WalaVarExpr(ssa.getUse(1))));*/
    }

    Operation.Operator translateUnaryOp(IUnaryOpInstruction.Operator op) {
        switch(op) {
            case NEG: return Operation.Operator.NEG;
        }
        throw new IllegalArgumentException("Unknown Operator: " + op.toString() + " in translateUnaryOp");
    }

    @Override
    public void visitUnaryOp(SSAUnaryOpInstruction ssa) {
        veriStatement = new AssignmentStmt(new WalaVarExpr(ssa.getDef()),
                new Operation(
                        translateUnaryOp((IUnaryOpInstruction.Operator)ssa.getOpcode()),
                                convertWalaVar(ssa.getUse(0)))
                );
    }

    /*
        MWW: casts in SPF involve object creation, so are beyond what we can support currently in
        Static regions.
     */
    @Override
    public void visitConversion(SSAConversionInstruction ssa) {
        canVeritest = false;
        // veriStatement = new gov.nasa.jpf.symbc.veritesting.ast.def.ConversionInstruction(ssa);
    }


    @Override
    public void visitComparison(SSAComparisonInstruction ssa) {
        Expression expr;
        Expression condlhs = convertWalaVar(ssa.getUse(0));
        Expression condrhs = convertWalaVar(ssa.getUse(1));
        Operation.Operator condOp =
                (ssa.getOperator() == IComparisonInstruction.Operator.CMP ||
                        ssa.getOperator() == IComparisonInstruction.Operator.CMPG) ?
                        Operation.Operator.GT :
                        Operation.Operator.LT ;
        Expression rhs = new IfThenElseExpr(
                new Operation(condOp, condlhs, condrhs),
                Operation.ONE,
                new IfThenElseExpr(
                        new Operation(Operation.Operator.EQ, condlhs, condrhs),
                        Operation.ZERO,
                        new IntConstant(-1)));


        veriStatement =
                new AssignmentStmt(new WalaVarExpr(ssa.getDef()), rhs);
    }

    @Override
    public void visitConditionalBranch(SSAConditionalBranchInstruction ssa) {
        throw new IllegalArgumentException("Reached conditional branch in SSAToStatIVisitor: why?");
    }

    @Override
    public void visitSwitch(SSASwitchInstruction ssaSwitchInstruction) {
        canVeritest = false;
    }

    @Override
    public void visitReturn(SSAReturnInstruction ssaReturnInstruction) {
        veriStatement = new ReturnInstruction(ssaReturnInstruction);
    }

    @Override
    public void visitGet(SSAGetInstruction ssaGetInstruction) {
        veriStatement = new GetInstruction(ssaGetInstruction);
    }

    @Override
    public void visitPut(SSAPutInstruction ssaPutInstruction) {
        veriStatement = new PutInstruction(ssaPutInstruction);
    }

    @Override
    public void visitInvoke(SSAInvokeInstruction ssaInvokeInstruction) {
        veriStatement = new InvokeInstruction(ssaInvokeInstruction);
    }

    @Override
    public void visitNew(SSANewInstruction ssaNewInstruction) {
        veriStatement = new NewInstruction(ssaNewInstruction);
    }

    @Override
    public void visitArrayLength(SSAArrayLengthInstruction ssaArrayLengthInstruction) {
        veriStatement = new gov.nasa.jpf.symbc.veritesting.ast.def.ArrayLengthInstruction(ssaArrayLengthInstruction);
    }

    @Override
    public void visitThrow(SSAThrowInstruction ssaThrowInstruction) {
        veriStatement = new ThrowInstruction(ssaThrowInstruction);
    }

    @Override
    public void visitMonitor(SSAMonitorInstruction ssaMonitorInstruction) {
        canVeritest = false;
    }

    @Override
    public void visitCheckCast(SSACheckCastInstruction ssaCheckCastInstruction) {
        veriStatement = new CheckCastInstruction(ssaCheckCastInstruction);
    }

    @Override
    public void visitInstanceof(SSAInstanceofInstruction ssaInstanceofInstruction) {
        veriStatement = new InstanceOfInstruction(ssaInstanceofInstruction);
    }

    @Override
    public void visitPhi(SSAPhiInstruction ssaPhiInstruction) {
        try {
            veriStatement = translatePhi(ssaPhiInstruction);
        } catch (StaticRegionException sre) {
            pending = sre;
            canVeritest = false;
        }
    }

    @Override
    public void visitPi(SSAPiInstruction ssaPiInstruction) {
        veriStatement = SkipStmt.skip;
    }

    @Override
    public void visitGetCaughtException(SSAGetCaughtExceptionInstruction ssaGetCaughtExceptionInstruction) {
        canVeritest = false;
    }

    @Override
    public void visitLoadMetadata(SSALoadMetadataInstruction ssaLoadMetadataInstruction) {
        canVeritest = false;
    }

    public static StaticRegionException sre = new StaticRegionException("Untranslatable instruction in SSAToStatIVisitor");

    public Stmt convert(SSAInstruction ssa) throws StaticRegionException {
        ssa.visit(this);
        if (!this.canVeritest) {
            if (pending != null) throw pending;
            throw sre;
        }
        else return this.veriStatement;
    }

    /*
    public static Stmt convert(SSAInstruction ssa) throws StaticRegionException {
        SSAToStatIVisitor visitor = new SSAToStatIVisitor();
        ssa.visit(visitor);
        if (!visitor.canVeritest) { throw sre; }
        else return visitor.veriStatement;
    }
    */
}

