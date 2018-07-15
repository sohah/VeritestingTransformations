/*******************************************************************************
 * Copyright (c) 2002 - 2006 IBM Corporation.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/
package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.SSAInstructions;

import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAInstructionFactory;
import com.ibm.wala.ssa.SymbolTable;
import com.ibm.wala.types.TypeReference;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.Var;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpression;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpressionVisitor;

/**
 * A dynamic type test (instanceof) instruction.
 */
public class SSAInstanceofInstruction implements VeriExpression {
    private final int iindex;
    private final Var result;

    private final VeriExpression ref;

    private final TypeReference checkedType;

    public SSAInstanceofInstruction(int iindex, Var result, VeriExpression ref, TypeReference checkedType) {
        this.iindex = iindex;
        this.result = result;
        this.ref = ref;
        this.checkedType = checkedType;
    }

    public Var getResult() {
        return result;
    }

    public VeriExpression getRef() {
        return ref;
    }

    public TypeReference getCheckedType() {
        return checkedType;
    }

    public int getIindex() {
        return iindex;
    }


    @Override
    public String toString() {
        return result + " = instanceof " + ref + " " + checkedType;
    }

    @Override
    public void visit(VeriExpressionVisitor v) {
        v.visitInstanceOfSSA(this);
    }
}
