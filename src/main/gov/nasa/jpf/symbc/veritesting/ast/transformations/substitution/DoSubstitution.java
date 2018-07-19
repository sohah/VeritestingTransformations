package gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution;

import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.PrettyPrintVisitor;
import gov.nasa.jpf.vm.ThreadInfo;

import java.util.HashMap;
import java.util.Set;

public class VarSubstitution {

    private ThreadInfo ti;
    private HashMap<String, Region> veriRegions;

    public VarSubstitution(ThreadInfo ti, HashMap<String, Region> veriRegions) {
        this.ti = ti;
        this.veriRegions = veriRegions;
    }

    public void doSubstitution() {
        Set<String> keys = veriRegions.keySet();
        for (String key: keys) {
            Region region = veriRegions.get(key);
            ExprSubstitutionVisitor substitutionVisitor = new ExprSubstitutionVisitor(ti, region);
            AstMapVisitor mapVisitor = new AstMapVisitor(substitutionVisitor);
            region.stmt.accept(mapVisitor);
            System.out.println("Printing regions after substitution:");
            System.out.println(PrettyPrintVisitor.print(region.stmt));
        }
    }
}
