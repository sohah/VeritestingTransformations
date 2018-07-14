package gov.nasa.jpf.symbc.veritesting.AstTransformation;

import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSAInstruction;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements.Composition;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements.VeriStatement;
import gov.nasa.jpf.symbc.veritesting.VeritestingException;

import java.util.List;

public class BBTransform {
    //this is the last composed statement where we might want to expand/compose with something else later in the transformation.
    VeriStatement continuation;

    VeriStatement transformBasicBlock(SSACFG.BasicBlock bb) throws VeritestingException {
        List<SSAInstruction> instList = bb.getAllInstructions();
        return transformInstList(instList);
    }

    private VeriStatement transformInstList(List<SSAInstruction> instList) {
        VeriStatement s1 = null;
        try{
             s1 = transformInstruction(instList.get(0));
             if(instList.size()==1)
                 this.continuation = s1;
        }catch (VeritestingException exception){
            System.out.println("Veritesting Exception is raised during first(AST) transformation.!!");
        }
        VeriStatement s2 = transformInstList(instList.subList(1,instList.size()));
        return new Composition(s1, s2);
    }

    private VeriStatement transformInstruction(SSAInstruction instruction) throws VeritestingException {
        SSAToStatIVisitor toStatVisitor = new SSAToStatIVisitor();
        instruction.visit(toStatVisitor);
        if (!toStatVisitor.canVeritest)
            throw new VeritestingException("Could not translate CFG to AST");
        else
            return toStatVisitor.veriStatement;
    }
}
