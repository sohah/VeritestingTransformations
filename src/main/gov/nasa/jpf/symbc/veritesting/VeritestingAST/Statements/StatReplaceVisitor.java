package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements;


//SH: This visitor is used to replace a part of the AST
public class StatReplaceVisitor implements VeriStatVisitor{
    private VeriStatment oldStatement;
    private VeriStatment newStatement;

    public StatReplaceVisitor(VeriStatment oldStatement, VeriStatment newStatement) {
        this.oldStatement = oldStatement;
        this.newStatement = newStatement;
    }


    @Override
    public Object visitSPFCase(SPFCase spfCase) {
        if(spfCase.equals(oldStatement))
            return newStatement;
        else
            return spfCase;
    }

    @Override
    public Object visitSkip(Skip skip) {
        if(skip.equals(oldStatement))
            return newStatement;
        else
            return skip;
    }

    @Override
    public Object visitIfThenElse(IfThenElse ifThenElse) {
        if(ifThenElse.equals(oldStatement)) {
            return newStatement;
        } else{
            VeriStatment newS1 = (VeriStatment) ifThenElse.getS1().visit(this);
            VeriStatment newS2 = (VeriStatment) ifThenElse.getS2().visit(this);
            ifThenElse.setS1(newS1);
            ifThenElse.setS2(newS2);
            return ifThenElse;
        }
    }

    @Override
    public Object visitComposition(Composition composition) {
        if(composition.equals(oldStatement)) {
            return newStatement;
        } else{
            VeriStatment newS1 = (VeriStatment) composition.getS1().visit(this);
            VeriStatment newS2 = (VeriStatment) composition.getS2().visit(this);
            composition.setS1(newS1);
            composition.setS2(newS2);
            return composition;
        }
    }

    @Override
    public Object visitAssignment(Assignment assignment) {
        if(assignment.equals(oldStatement))
            return newStatement;
        else
            return assignment;
    }
}
