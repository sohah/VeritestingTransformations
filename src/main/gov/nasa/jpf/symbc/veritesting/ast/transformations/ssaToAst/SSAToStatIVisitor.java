package gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst;

import com.ibm.wala.shrikeBT.IBinaryOpInstruction;
import com.ibm.wala.shrikeBT.IComparisonInstruction;
import com.ibm.wala.shrikeBT.IUnaryOpInstruction;
import com.ibm.wala.ssa.*;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import za.ac.sun.cs.green.expr.*;

import java.util.*;

import static gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.SSAToStatIVisitor.sre;


//SH: This class translates SSAInstructions to Veritesting Statements.
// many of the assignment instructions have the left hand side as an "EmptyVar" because none
// has been constructed at this point yet.


public class SSAToStatIVisitor implements SSAInstruction.IVisitor {
    public Stmt veriStatement;
    public boolean canVeritest = true;

    private IR ir;
    private HashMap<ISSABasicBlock, List<Expression>> blockConditionMap;
    private Deque<Expression> currentCondition;
    private ISSABasicBlock currentBlock;
    private StaticRegionException pending = null;

    public SSAToStatIVisitor(IR ir,
                             ISSABasicBlock currentBlock,
                             HashMap<ISSABasicBlock, List<Expression>> blockConditionMap,
                             Deque<Expression> currentCondition) {
        this.ir = ir;
        this.currentBlock = currentBlock;
        this.blockConditionMap = blockConditionMap;
        this.currentCondition = currentCondition;

    }

/*
    Beginning of methods for translating Phi instructions...
 */

    private Expression convertWalaVar(int ssaVar) throws StaticRegionException {
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
            return new WalaVarExpr(ssaVar);
        }
    }

    private List<List<Expression>> simplifyConditions(List<List<Expression>> conds) {
        assert (conds != null);

        // check whether there are shared conditions across all incoming branches
        // This can happen on an inner \phi
        Expression sharedCondElem = conds.get(0).get(0);
        for (List<Expression> cond: conds) {
            if (cond.get(0) != sharedCondElem) { return conds; }
        }
        // All conditions match on first element - remove it, then try again.
        List<List<Expression>> newConds = new ArrayList<List<Expression>>();
        for (List<Expression> cond: conds) {
            List<Expression> newCond = new ArrayList<>(cond.size() - 1);
            for (int i = 1; i < cond.size(); i++) {
                newCond.add(cond.get(i));
            }
        }
        return simplifyConditions(newConds);
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

    private Expression createGamma(List<List<Expression>> conds, List<Expression> values, int index) {
        if (index == conds.size() - 1) {
            return values.get(index);
        } else {
            return new GammaVarExpr(conjunct(conds.get(index)), values.get(index), createGamma(conds, values, index+1));
        }
    }

    public Stmt translatePhi(SSAPhiInstruction ssaphi) throws StaticRegionException {
        SSACFG cfg = ir.getControlFlowGraph();
        SymbolTable symtab = ir.getSymbolTable();
        Collection<ISSABasicBlock> preds = cfg.getNormalPredecessors(currentBlock);
        if (ssaphi.getNumberOfUses() != preds.size()) {
            throw new StaticRegionException("translateTruncatedFinalBlock: normal predecessors size does not match number of phi branches");
        }
        else {
            Iterator<ISSABasicBlock> it = preds.iterator();
            List<List<Expression>> conds = new ArrayList<List<Expression>>();
            List<Expression> values = new ArrayList<Expression>();

            for (int i = 0; i < ssaphi.getNumberOfUses(); i++) {
                int ssaVar = ssaphi.getUse(i);
                ISSABasicBlock preBlock = it.next();

                List<Expression> cond = blockConditionMap.get(preBlock);
                if (cond == null) {
                    // MWW TODO: this may be o.k. - we have an unstructured jump into our region.
                    //     TODO: But it is a little weird, so I don't want to incorrectly handle something.
                    throw new StaticRegionException("translateTruncatedFinalBlock: normal predecessor not found in blockConditionMap!");
                }
                else {
                    conds.add(cond);
                    values.add(convertWalaVar(ssaVar));
                }
            }
            // create Gamma statement
            conds = simplifyConditions(conds);
            return new AssignmentStmt(new WalaVarExpr(ssaphi.getDef()), createGamma(conds, values, 0));
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
        Expression op1 = new WalaVarExpr(ssa.getUse(0));
        Expression op2 = new WalaVarExpr(ssa.getUse(1));
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
                                new WalaVarExpr(ssa.getUse(0)))
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
        Expression condlhs = new WalaVarExpr(ssa.getUse(0));
        Expression condrhs = new WalaVarExpr(ssa.getUse(1));
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

