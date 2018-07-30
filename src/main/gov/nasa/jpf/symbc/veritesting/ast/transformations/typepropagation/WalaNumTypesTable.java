package gov.nasa.jpf.symbc.veritesting.ast.transformations.typepropagation;

import gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution.Table;

public class WalaNumTypesTable extends Table<String> {
    public WalaNumTypesTable() {
        super("WalaNumTypesTable", "Wala value number", "type name");
    }
}
