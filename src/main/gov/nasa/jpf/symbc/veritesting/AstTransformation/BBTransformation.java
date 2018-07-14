package gov.nasa.jpf.symbc.veritesting.AstTransformation;

import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSAInstruction;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements.Composition;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements.VeritestingStatement;
import gov.nasa.jpf.symbc.veritesting.VeritestingException;

import java.util.List;

public class BBTransformation {
    VeritestingStatement continuation;

    VeritestingStatement transformBasicBlock(SSACFG.BasicBlock bb) throws VeritestingException {
        List<SSAInstruction> instList = bb.getAllInstructions();
        return transformInstList(instList);
    }

    private VeritestingStatement transformInstList(List<SSAInstruction> instList) {
        VeritestingStatement s1 = null;
        try{
             s1 = transformInstruction(instList.get(0));
             if(instList.size()==1)
                 this.continuation = s1;
        }catch (VeritestingException exception){
            System.out.println("Veritesting Exception is raised during first(AST) transformation.!!");
        }
        VeritestingStatement s2 = transformInstList(instList.subList(1,instList.size()));
        return new Composition(s1, s2);
    }

    private VeritestingStatement transformInstruction(SSAInstruction instruction) throws VeritestingException {
        ToStatementIVisitor toStatVisitor = new ToStatementIVisitor();
        instruction.visit(toStatVisitor);
        if (!toStatVisitor.canVeritest)
            throw new VeritestingException("Could not translate CFG to AST");
        else
            return toStatVisitor.veritestingStatement;
    }
}
