package gov.nasa.jpf.symbc.veritesting.AstTransformation;

import com.ibm.wala.ssa.ISSABasicBlock;
import com.ibm.wala.ssa.SSAInstruction;
import gov.nasa.jpf.symbc.veritesting.AstTransformation.CFGConversion.SSAToStatIVisitor;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements.CompositionStmt;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements.SkipStmt;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements.Stmt;
import gov.nasa.jpf.symbc.veritesting.VeritestingException;


import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

//SH: this class is used to transform a single basic block with all its internal instructions.
// and becasue constructing next blocks requires a change to the inner most statement, a "continuation" is used to represent that.

public class BBTransform {
    //this is the last composed statement where we might want to expand/compose with something else later in the transformation.
    Stmt continuation;

    Stmt transformBasicBlock(ISSABasicBlock bb) {
        Iterator<SSAInstruction> instructionIterator = bb.iterator();
        List<SSAInstruction> instList = new ArrayList<>();
        while(instructionIterator.hasNext())
            instList.add(instructionIterator.next());
        if(instList.size()  == 0)
            return (SkipStmt.skip);
        else
            return transformInstList(instList);
    }

    private Stmt transformInstList(List<SSAInstruction> instList) {
        Stmt s1 = null;
        try{
             s1 = transformInstruction(instList.get(0));
             if(instList.size()==1){
                 this.continuation = s1;
                 return s1;
             }
        }catch (VeritestingException exception){
            System.out.println("Veritesting Exception is raised during first(AST) transformation.!!");
        }
        Stmt s2 = transformInstList(instList.subList(1,instList.size()));
        return new CompositionStmt(s1, s2);
    }

    private Stmt transformInstruction(SSAInstruction instruction) throws VeritestingException {
        SSAToStatIVisitor toStatVisitor = new SSAToStatIVisitor();
        instruction.visit(toStatVisitor);
        if (!toStatVisitor.canVeritest)
            throw new VeritestingException("Could not translate CFG to AST");
        else
            return toStatVisitor.veriStatement;
    }
}
