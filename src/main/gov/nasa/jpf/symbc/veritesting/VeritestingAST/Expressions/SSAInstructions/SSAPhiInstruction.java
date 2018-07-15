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

import com.ibm.wala.analysis.stackMachine.AbstractIntStackMachine;
import com.ibm.wala.cfg.ControlFlowGraph;
import com.ibm.wala.ssa.*;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.Var;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpression;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpressionVisitor;

import java.util.Arrays;
import java.util.Iterator;

public class SSAPhiInstruction implements VeriExpression {
    private final Var result;
    private final int iindex;

    private final Var[] params;


    public int getIindex() {
        return iindex;
    }

    public Var getResult() {
        return result;
    }

    public Var[] getParams() {
        return params;
    }

    public SSAPhiInstruction(int iindex, Var result, Var[] params) {
        this.iindex = iindex;
        this.result = result;
        this.params = params;
    }


    @Override
    public String toString() {
        StringBuffer s = new StringBuffer();

        s.append(result).append(" = phi ");
        s.append(" ").append(params[0]);
        for (int i = 1; i < params.length; i++) {
            s.append(",").append(params[i]);
        }
        return s.toString();
    }

    @Override
    public void visit(VeriExpressionVisitor v) {
        v.visitPhiSSA(this);
    }

}
