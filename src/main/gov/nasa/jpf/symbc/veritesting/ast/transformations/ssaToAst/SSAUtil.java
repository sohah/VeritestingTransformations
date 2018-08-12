package gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst;

import com.ibm.wala.shrikeBT.IConditionalBranchInstruction;
import com.ibm.wala.ssa.*;
import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;
import za.ac.sun.cs.green.expr.*;

import java.util.ArrayList;
import java.util.Collection;
import java.util.PriorityQueue;

/**
 * Some utility methods used during construction of the StaticRegion.
 */
public class SSAUtil {

    public static Collection<ISSABasicBlock> getNonReturnSuccessors(SSACFG cfg, ISSABasicBlock current) {
        SSAInstruction last = current.getLastInstruction();
        if (!(last instanceof SSAReturnInstruction) && !(last instanceof SSAThrowInstruction)) {
            return cfg.getNormalSuccessors(current);
        }
        else {
            return new ArrayList<>();
        }
    }

    public static PriorityQueue<ISSABasicBlock> constructSortedBlockPQ() {
        return new PriorityQueue<>((ISSABasicBlock o1, ISSABasicBlock o2)->o1.getNumber()-o2.getNumber());
    }

    public static <E> void enqueue(PriorityQueue<E> queue, E elem) {
        if (!queue.contains(elem)) {
            queue.add(elem);
        }
    }

    public static boolean isConditionalBranch(ISSABasicBlock current) {
        return current.getLastInstruction() instanceof SSAConditionalBranchInstruction;
    }

    public static SSAConditionalBranchInstruction getLastBranchInstruction(ISSABasicBlock current) {
        assert(current.getLastInstruction() instanceof SSAConditionalBranchInstruction);
        return (SSAConditionalBranchInstruction)current.getLastInstruction();
    }

    public static void printBlock(ISSABasicBlock block) {
        System.out.println("Basic block: " + block);
        for (SSAInstruction ins: block) {
            System.out.println("  Instruction: " + ins);
        }
        System.out.println("End of block: " + block);
    }

    public static void printBlocksUpTo(SSACFG cfg, int blockNum) {
        for (int i = 1; i <= blockNum; i++) {
            printBlock(cfg.getNode(i));
        }
    }

    // This is so dumb, but I don't know how to count instructions!
    // WALA is not very helpful for this; the multiple instruction
    // index values correspond to a single WALA instruction.

    public static boolean statefulBlock(ISSABasicBlock block) {
        int count = 0;
        for (SSAInstruction ins: block) {
            count++;
            if (count >= 2) return true;
        }
        return false;
    }


    public static Operation.Operator convertOperator(IConditionalBranchInstruction.Operator operator) {
        switch (operator) {
            case EQ: return Operation.Operator.EQ;
            case NE: return Operation.Operator.NE;
            case LT: return Operation.Operator.LT;
            case GE: return Operation.Operator.GE;
            case GT: return Operation.Operator.GT;
            case LE: return Operation.Operator.LE;
        }
        throw new IllegalArgumentException("convertOperator does not understand operator: " + operator);
    }

    public static Expression convertWalaVar(IR ir, int ssaVar) {
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

    public static Expression convertCondition(IR ir, SSAConditionalBranchInstruction cond) {
        return new Operation(
                convertOperator((IConditionalBranchInstruction.Operator)cond.getOperator()),
                convertWalaVar(ir, cond.getUse(0)),
                convertWalaVar(ir, cond.getUse(1)));
    }

}