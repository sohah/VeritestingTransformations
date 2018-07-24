package gov.nasa.jpf.symbc.veritesting.ast.transformations.linearization;

import gov.nasa.jpf.symbc.veritesting.ast.def.Region;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.DefaultTransformation;

public class LinearizationTransformation extends DefaultTransformation {

    @Override
    public Region execute(Region region) {
        LinearizationVisitor v = new LinearizationVisitor();
        Stmt stmt = region.stmt.accept(v);
        return new Region(stmt, region.ir, region.stackSlotMap, region.valueMap);
    }
}
