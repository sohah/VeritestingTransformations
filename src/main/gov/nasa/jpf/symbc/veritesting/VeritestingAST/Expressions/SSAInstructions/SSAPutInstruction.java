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

import com.ibm.wala.ssa.SSAFieldAccessInstruction;
import com.ibm.wala.types.FieldReference;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.Var;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpression;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpressionVisitor;

/**
 * A putfield or putstatic instruction
 */
public class SSAPutInstruction implements VeriExpression {

    private final int iindex;
    private final VeriExpression val;
    private final Var ref;
    private final FieldReference field;
    private final boolean isStatic;

    public SSAPutInstruction(int iindex, Var ref, VeriExpression val, FieldReference field, boolean isStatic) {
        this.iindex = iindex;
        this.ref = ref;
        this.val = val;
        this.field = field;
        this.isStatic = isStatic;
    }


    public VeriExpression getVal() {
        return val;
    }


    public int getIindex() {
        return iindex;
    }

    public Var getRef() {
        return ref;
    }

    public FieldReference getField() {
        return field;
    }

    public boolean isStatic() {
        return isStatic;
    }

    @Override
    public String toString() {
        if (isStatic()) {
            return "putstatic " + getField() + " = " + val;
        } else {
            return "putfield " + getRef() + "." + getField() + " = " + val;
        }
    }

    @Override
    public void visit(VeriExpressionVisitor v) {
        v.visitPutInstruction(this);
    }


}
