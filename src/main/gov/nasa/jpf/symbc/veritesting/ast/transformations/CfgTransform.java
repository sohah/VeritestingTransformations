package gov.nasa.jpf.symbc.veritesting.ast.transformations;

import com.ibm.wala.ssa.ISSABasicBlock;
import com.ibm.wala.ssa.SSACFG;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.VeritestingException;

import java.util.List;

//SH: This class is used to tranform the CFG

/*
public class CfgTransform {
    private SSACFG cfg;

    public CfgTransform(SSACFG cfg) {
        this.cfg = cfg;
    }


    public Stmt transform(ISSABasicBlock bbStart, ISSABasicBlock bbEnd) throws VeritestingException {
        Stmt statement = null;
        List<ISSABasicBlock> succList = (List<ISSABasicBlock>) cfg.getNormalSuccessors(bbStart);
        if(!bbStart.equals(bbEnd)) {
            BBTransform bbTransform = new BBTransform();
            Stmt currBBStat = bbTransform.transformBasicBlock(bbStart);
            Stmt continuation = bbTransform.continuation;
            switch (succList.size()) {
                case 1:{
                    Stmt nextStat = transform(succList.get(0),bbEnd);
                    Stmt subAst  = new CompositionStmt(continuation, nextStat);
                    StatReplaceVisitor replaceVisitor = new StatReplaceVisitor(continuation, subAst);
                    statement = (Stmt) currBBStat.visit(replaceVisitor);;
                    break;
                }
                case 2: {
                    assert (continuation instanceof IfThenElseStmt);
                    ISSABasicBlock ipdm = cfg.getIPdom(bbStart.getNumber());
                    Stmt nextStat1 = transform(succList.get(0), ipdm);
                    Stmt nextStat2 = transform(succList.get(1), ipdm);
                    ((IfThenElseStmt) continuation).setS1(nextStat1);
                    ((IfThenElseStmt) continuation).setS2(nextStat2);

                    Stmt ipdmStat = transform(ipdm, bbEnd);
                    Stmt subAst = new CompositionStmt(continuation, ipdmStat);
                    StatReplaceVisitor replaceVisitor = new StatReplaceVisitor(continuation, subAst);
                    statement = (Stmt) currBBStat.visit(replaceVisitor);
                    break;
                }
                default:
                    throw new VeritestingException("Unexpected number of successors during AST Transformation.!");
            }
        }
        else{
            return (new SkipStmt());
        }
        return statement;
    }
}
*/