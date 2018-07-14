package gov.nasa.jpf.symbc.veritesting.AstTransformation;

import com.ibm.wala.ssa.ISSABasicBlock;
import com.ibm.wala.ssa.SSAInstruction;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements.Composition;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements.Skip;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements.VeriStatment;
import gov.nasa.jpf.symbc.veritesting.VeritestingException;


import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

//SH: this class is used to transform a single basic block with all its internal instructions.
// and becasue constructing next blocks requires a change to the inner most statement, a "continuation" is used to represent that.

public class BBTransform {
    //this is the last composed statement where we might want to expand/compose with something else later in the transformation.
    VeriStatment continuation;

    VeriStatment transformBasicBlock(ISSABasicBlock bb) {
        Iterator<SSAInstruction> instructionIterator = bb.iterator();
        List<SSAInstruction> instList = new ArrayList<>();
        while(instructionIterator.hasNext())
            instList.add(instructionIterator.next());
        if(instList.size()  == 0)
            return (new Skip());
        else
            return transformInstList(instList);
    }

    private VeriStatment transformInstList(List<SSAInstruction> instList) {
        VeriStatment s1 = null;
        try{
             s1 = transformInstruction(instList.get(0));
             if(instList.size()==1){
                 this.continuation = s1;
                 return s1;
             }
        }catch (VeritestingException exception){
            System.out.println("Veritesting Exception is raised during first(AST) transformation.!!");
        }
        VeriStatment s2 = transformInstList(instList.subList(1,instList.size()));
        return new Composition(s1, s2);
    }

    private VeriStatment transformInstruction(SSAInstruction instruction) throws VeritestingException {
        SSAToStatIVisitor toStatVisitor = new SSAToStatIVisitor();
        instruction.visit(toStatVisitor);
        if (!toStatVisitor.canVeritest)
            throw new VeritestingException("Could not translate CFG to AST");
        else
            return toStatVisitor.veriStatement;
    }
}
