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

import com.ibm.wala.types.TypeReference;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpression;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpressionVisitor;

/**
 * SSA instruction representing an array store.
 */
public class SSAArrayStoreInstruction implements VeriExpression {

    private final VeriExpression value;

    private final VeriExpression arrayref;
    private final int index;
    private final TypeReference elementType;
    private final int iindex;

    protected SSAArrayStoreInstruction(int iindex, VeriExpression arrayref, int index, VeriExpression value, TypeReference elementType) {
        this.value = value;
        this.arrayref = arrayref;
        this.index = index;
        this.elementType = elementType;
        this.iindex = iindex;
    }

    public VeriExpression getValue() {
        return value;
    }

    public VeriExpression getArrayref() {
        return arrayref;
    }

    public int getIndex() {
        return index;
    }

    public TypeReference getElementType() {
        return elementType;
    }

    public int getIindex() {
        return iindex;
    }

    @Override
    public void visit(VeriExpressionVisitor v) {
        v.visitArrayStore(this);
    }

    @Override
    public String toString() {
        return "arraystore " + getArrayref() + "[" + getIndex() + "] = " + value;
    }

}
