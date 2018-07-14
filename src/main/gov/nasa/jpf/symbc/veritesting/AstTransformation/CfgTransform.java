package gov.nasa.jpf.symbc.veritesting.AstTransformation;

import com.ibm.wala.ssa.ISSABasicBlock;
import com.ibm.wala.ssa.SSACFG;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements.*;
import gov.nasa.jpf.symbc.veritesting.VeritestingException;

import java.util.List;


public class CfgTransform {
    private SSACFG cfg;

    public CfgTransform(SSACFG cfg) {
        this.cfg = cfg;
    }


    public VeriStatment transform(ISSABasicBlock bbStart, ISSABasicBlock bbEnd) throws VeritestingException {
        VeriStatment statement = null;
        List<ISSABasicBlock> succList = (List<ISSABasicBlock>) cfg.getNormalSuccessors(bbStart);
        if(!bbStart.equals(bbEnd)) {
            BBTransform bbTransform = new BBTransform();
            VeriStatment currBBStat = bbTransform.transformBasicBlock(bbStart);
            VeriStatment continuation = bbTransform.continuation;
            switch (succList.size()) {
                case 1:{
                    VeriStatment nextStat = transform(succList.get(0),bbEnd);
                    VeriStatment subAst  = new Composition(continuation, nextStat);
                    StatReplaceVisitor replaceVisitor = new StatReplaceVisitor(continuation, subAst);
                    statement = (VeriStatment) currBBStat.visit(replaceVisitor);;
                    break;
                }
                case 2: {
                    assert (continuation instanceof IfThenElse);
                    ISSABasicBlock ipdm = cfg.getIPdom(bbStart.getNumber());
                    VeriStatment nextStat1 = transform(succList.get(0), bbEnd);
                    VeriStatment nextStat2 = transform(succList.get(1), bbEnd);
                    ((IfThenElse) continuation).setS1(nextStat1);
                    ((IfThenElse) continuation).setS2(nextStat2);

                    VeriStatment ipdmStat = transform(ipdm, bbEnd);
                    VeriStatment subAst = new Composition(continuation, ipdmStat);
                    StatReplaceVisitor replaceVisitor = new StatReplaceVisitor(continuation, subAst);
                    statement = (VeriStatment) currBBStat.visit(replaceVisitor);
                    break;
                }
                default:
                    throw new VeritestingException("Unexpected number of successors during AST Transformation.!");
            }
        }
        else{
            return (new Skip());
        }
        return statement;
    }
}
