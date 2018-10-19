package gov.nasa.jpf.symbc.veritesting.ChoiceGenerator;

import gov.nasa.jpf.jvm.bytecode.IfInstruction;
import gov.nasa.jpf.symbc.VeritestingListener;
import gov.nasa.jpf.symbc.bytecode.IFNONNULL;
import gov.nasa.jpf.symbc.numeric.*;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.SpfUtil;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.CreateStaticRegions;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.MethodInfo;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Operation;

import static gov.nasa.jpf.symbc.VeritestingListener.statisticManager;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.isPCSat;


public class StaticBranchChoiceGenerator extends StaticPCChoiceGenerator {

    Object[] spfSlotAttr;

    public static final int STATIC_CHOICE = 0;
    public static final int THEN_CHOICE = 1;
    public static final int ELSE_CHOICE = 2;
    public static final int RETURN_CHOICE = 3;

    public StaticBranchChoiceGenerator(DynamicRegion region, Instruction instruction) {
        super(2, region, instruction);
        Kind kind = getKind(instruction);

        assert (kind == Kind.BINARYIF ||
                kind == Kind.NULLIF ||
                kind == Kind.UNARYIF);
    }

    // MWW: make choice 0 and choice 4 also the responsibility of the CG
    public Instruction execute(ThreadInfo ti, Instruction instructionToExecute, int choice) throws StaticRegionException {
        // if/else conditions.
        assert (choice == STATIC_CHOICE || choice == THEN_CHOICE || choice == ELSE_CHOICE);

        Instruction nextInstruction = null;
        if (choice == STATIC_CHOICE) {
            collectSpfStackFrame();
            System.out.println("\n=========Executing static region choice in BranchCG");
            nextInstruction = VeritestingListener.setupSPF(ti, instructionToExecute, getRegion());
            MethodInfo methodInfo = instructionToExecute.getMethodInfo();
            String className = methodInfo.getClassName();
            String methodName = methodInfo.getName();
            String methodSignature = methodInfo.getSignature();
            int offset = instructionToExecute.getPosition();
            String key = CreateStaticRegions.constructRegionIdentifier(className + "." + methodName + methodSignature, offset);
            statisticManager.updateVeriSuccForRegion(key);
            ++VeritestingListener.veritestRegionCount;
        } else if (choice == THEN_CHOICE || choice == ELSE_CHOICE) {
           // ti.getTopFrame().defreeze();
            //restoreSpfStackFrame();
            System.out.println("\n=========Executing" + (choice == THEN_CHOICE ? " then " : " else ") + ".  Instruction: ");
            switch (getKind(instructionToExecute)) {
                case UNARYIF:
                    nextInstruction = executeUnaryIf(instructionToExecute, choice);
                    break;
                case BINARYIF:
                    nextInstruction = executeBinaryIf(instructionToExecute, choice);
                    break;
                case NULLIF:
                    nextInstruction = executeNullIf(instructionToExecute);
                    break;
                case OTHER:
                    throw new StaticRegionException("Error: Branch choice generator instantiated on non-branch instruction!");
            }
        } else {
            // should never get here (until we make early returns)
            assert (false);
        }
        return nextInstruction;
    }

    private void restoreSpfStackFrame() {

        int slotSize = spfSlotAttr.length;

        for (int i = 0; i < slotSize; i++) {
            ti.getTopFrame().setSlotAttr(i, spfSlotAttr[i]);
        }
    }

    /**
     * The puprose of this function is to collect the stack slot state before running veritesting choice, so that if veritesting changed the slots attributes by populating its outputs, we would be able to restore the slots back to their original states when running the SPF then, and else choices.
     */
    private void collectSpfStackFrame() {
        spfSlotAttr = ti.getTopFrame().getSlotAttrs().clone();
    }

    /*
        So: here is what should happen.
        We have the PC constructed for choices 0, 1, and 2.
        In this case, we are in choice 1 or 2.

        We unpack the instruction, add it to the PC, and execute.
     */
    private Instruction executeBinaryIf(Instruction instruction, int choice) throws StaticRegionException {
        /*if(currentTopFrame != null)
            ti.setTopFrame(currentTopFrame); //retoring the stackframe for SPFCase
*/
        StackFrame sf = ti.getModifiableTopFrame();

        IntegerExpression sym_v1 = (IntegerExpression) sf.getOperandAttr(1);
        IntegerExpression sym_v2 = (IntegerExpression) sf.getOperandAttr(0);

        if ((sym_v1 == null) && (sym_v2 == null)) { // both conditions are concrete
            //System.out.println("Execute IF_ICMPEQ: The conditions are concrete");
            return instruction.execute(ti);
        } else {
            int v2 = sf.pop();
            int v1 = sf.pop();
            PathCondition pc;
            pc = this.getCurrentPC();

            assert pc != null;
            assert (choice == THEN_CHOICE || choice == ELSE_CHOICE);


            if (choice == ELSE_CHOICE) {
                Comparator byteCodeOp = SpfUtil.getComparator(instruction);
                if (sym_v1 != null) {
                    if (sym_v2 != null) { //both are symbolic values
                        pc._addDet(byteCodeOp, sym_v1, sym_v2);
                    } else
                        pc._addDet(byteCodeOp, sym_v1, v2);
                } else
                    pc._addDet(byteCodeOp, v1, sym_v2);
                boolean isPCSat = isPCSat(pc);
                if (!isPCSat) {// not satisfiable
                    ti.getVM().getSystemState().setIgnored(true);
                } else {
                    this.setCurrentPC(pc);
                }
                return ((IfInstruction) instruction).getTarget();
            } else {
                Comparator byteCodeNegOp = SpfUtil.getNegComparator(instruction);
                if (sym_v1 != null) {
                    if (sym_v2 != null) { //both are symbolic values
                        pc._addDet(byteCodeNegOp, sym_v1, sym_v2);
                    } else
                        pc._addDet(byteCodeNegOp, sym_v1, v2);
                } else
                    pc._addDet(byteCodeNegOp, v1, sym_v2);
                boolean isPCSat = isPCSat(pc);
                if (!isPCSat) {// not satisfiable
                    ti.getVM().getSystemState().setIgnored(true);
                } else {
                    this.setCurrentPC(pc);
                }
                return instruction.getNext(ti);
            }

        }
    }

    public Instruction executeNullIf(Instruction instruction) {

        StackFrame sf = ti.getModifiableTopFrame();
        Expression sym_v = (Expression) sf.getOperandAttr();
        if (sym_v == null) { // the condition is concrete
            //System.out.println("Execute IFEQ: The condition is concrete");
            return ((IFNONNULL) instruction).execute(ti);
        } else {
            sf.pop();
            return ((IfInstruction) instruction).getTarget();
        }
    }


    public Instruction executeUnaryIf(Instruction instruction, int choice) throws StaticRegionException {

        StackFrame sf = ti.getModifiableTopFrame();
        IntegerExpression sym_v = (IntegerExpression) sf.getOperandAttr();

        ti.getModifiableTopFrame().pop();
        if (sym_v == null) { // the condition is concrete
            return instruction.execute(ti);
        }
        PathCondition pc = this.getCurrentPC();
        if (choice == ELSE_CHOICE) {
            pc._addDet(SpfUtil.getComparator(instruction), sym_v, 0);
            boolean isPCSat = isPCSat(pc);
            if (!isPCSat) {// not satisfiable
                ti.getVM().getSystemState().setIgnored(true);
            } else {
                this.setCurrentPC(pc);
            }
            return ((IfInstruction) instruction).getTarget();
        } else {
            pc._addDet(SpfUtil.getNegComparator(instruction), sym_v, 0);
            boolean isPCSat = isPCSat(pc);
            if (!isPCSat) {// not satisfiable
                ti.getVM().getSystemState().setIgnored(true);
            } else {
                this.setCurrentPC(pc);
            }
            return instruction.getNext(ti);
        }
    }

    // 4 cases (they may be UNSAT, but that's ok):
    // 0: staticNominalNoReturn
    // 1: thenException
    // 2: elseException
    // 3: staticNominalReturn
    // NB: then and else constraints are the same (here).  We will tack on the additional
    // constraint for the 'then' and 'else' branches when we execute the choice generator.
    private PathCondition createPC(PathCondition pc, Expression regionSummary, Expression constraint) {
        PathCondition pcCopy = pc.make_copy();
        za.ac.sun.cs.green.expr.Expression copyConstraint = new Operation(Operation.Operator.AND, regionSummary, constraint);
        pcCopy._addDet(new GreenConstraint(copyConstraint));
        return pcCopy;
    }

    public void makeVeritestingCG(ThreadInfo ti) throws StaticRegionException {
        assert (region.regionSummary != null);
        PathCondition pc;
        if (ti.getVM().getSystemState().getChoiceGenerator() instanceof PCChoiceGenerator)
            pc = ((PCChoiceGenerator) (ti.getVM().getSystemState().getChoiceGenerator())).getCurrentPC();
        else {
            pc = new PathCondition();
            pc._addDet(new GreenConstraint(Operation.TRUE));
        }
        setPC(createPC(pc, region.regionSummary, new Operation(Operation.Operator.NOT, region.spfPredicateSummary)), STATIC_CHOICE);
        setPC(createPC(pc, region.regionSummary, region.spfPredicateSummary), THEN_CHOICE);
        setPC(createPC(pc, region.regionSummary, region.spfPredicateSummary), ELSE_CHOICE);
        // TODO: create the path predicate for the 'return' case.
    }

}
