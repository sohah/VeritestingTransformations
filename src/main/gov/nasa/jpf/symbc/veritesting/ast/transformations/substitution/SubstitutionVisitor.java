package gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution;

import com.ibm.wala.classLoader.CallSiteReference;
import com.ibm.wala.shrikeBT.IInvokeInstruction;
import com.ibm.wala.ssa.SSAInvokeInstruction;
import com.ibm.wala.ssa.SymbolTable;
import com.ibm.wala.types.MethodReference;
import com.ibm.wala.util.strings.Atom;
import gov.nasa.jpf.symbc.VeritestingListener;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.VeritestingMain;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.ValueSymbolTable;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.VarTypeTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Uniquness.UniqueRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.CreateStaticRegions;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticRegion;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitorAdapter;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.StmtPrintVisitor;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;
import za.ac.sun.cs.green.expr.Expression;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.SPFToGreenExpr;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.SpfUtil.createSPFVariableForType;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.WalaUtil.makeConstantFromWala;

/**
 * The Substitution Transformation is responsible for replacing all vars with their symbolic values if found, as well as the substitution of all constant vars.
 * Substitution Transformation is done in a general way depending on the type of the StaticRegion. Mainly by allowing the substitution to replace variables with values by looking up the ValueSymbolTable, where the ValueSymbolTable is filled depending on the type of the region. If the region is not a method region, the ValueSymbolTable is filled by a priori pass where all "input" var values are discovered by inquiring SPF for their stack slot attribute. If the region is a method region then the ValueSymbolTable is filled up by the caller by filling up vars/values of the parameters.
 * In this transformation, constants are also discovered as part of the process.
 */
public class SubstitutionVisitor extends AstMapVisitor {
    ExprVisitorAdapter<Expression> eva;
    public final ValueSymbolTable valueSymbolTable;
    public final StaticRegion staticRegion;
    public final ThreadInfo ti;

    private SubstitutionVisitor(ThreadInfo ti, StaticRegion staticRegion,
                                ValueSymbolTable valueSymbolTable) {

        super(new ExprSubstitutionVisitor(ti, staticRegion, valueSymbolTable));
        this.ti = ti;
        this.staticRegion = staticRegion;
        this.valueSymbolTable = valueSymbolTable;
        eva = super.eva;

    }


    @Override
    public Stmt visit(AssignmentStmt a) {
        return new AssignmentStmt(a.lhs, eva.accept(a.rhs));
    }

    @Override
    public Stmt visit(ArrayLoadInstruction c) {
        return new ArrayLoadInstruction(c.getOriginal(),
                eva.accept(c.arrayref),
                eva.accept(c.index),
                c.elementType,
                c.def);
    }

    @Override
    public Stmt visit(GetInstruction c) {
        return new GetInstruction(c.getOriginal(),
                c.def,
                eva.accept(c.ref),
                c.field);
    }

    @Override
    public Stmt visit(ArrayLengthInstruction c) {
        return new ArrayLengthInstruction(c.getOriginal(),
                c.def,
                eva.accept(c.arrayref));
    }

    @Override
    public Stmt visit(ReturnInstruction c) {
        return new ReturnInstruction(c.getOriginal(), eva.accept(c.rhs));
    }


    @Override
    public Stmt visit(PhiInstruction c) {

        Expression[] rhs = new Expression[c.rhs.length];
        for (int i = 0; i < rhs.length; i++) {
            rhs[i] = eva.accept(c.rhs[i]);
        }
        //hack here to populate the type of the def - there is an implicit side effect.
        eva.accept(c.def);

        return new PhiInstruction(c.getOriginal(),
                c.def,
                rhs);
    }

    /**
     * Visits an InvokeInstruction by attempting to inline static method regions.
     *
     * @param c Invoke Instruction to be visited.
     * @return A new statement that might include an inlined method region for static invocations.
     */

    @Override
    public Stmt visit(InvokeInstruction c) {

        ValueSymbolTable hgOrdValueSymbolTable = new ValueSymbolTable();
        Expression[] params = new Expression[c.params.length];
        for (int i = 0; i < params.length; i++) {
            params[i] = eva.accept(c.params[i]);
            hgOrdValueSymbolTable.add((i+1), params[i]); // in case of non static, the first parameter needs to be de-referenced because it will refer to an object class.
        }

        SSAInvokeInstruction instruction = c.getOriginal();
        IInvokeInstruction.IDispatch invokeCode = instruction.getCallSite().getInvocationCode();
        if (invokeCode == IInvokeInstruction.Dispatch.STATIC) {
            Pair<String, StaticRegion> keyRegionPair = findMethodStaticRegion(c);
            StaticRegion hgOrdStaticRegion = keyRegionPair.getSecond();
            if (hgOrdStaticRegion != null) {
                String key = keyRegionPair.getFirst();

                VeritestingListener.statisticManager.updateHitStatForRegion(key);

                System.out.println("\n********** High Order Region Discovered for region: " + key + "\n");
                System.out.println("\n---------- STARTING Inlining Transformation for region: ---------------\n" + StmtPrintVisitor.print(hgOrdStaticRegion.staticStmt) + "\n");
                StaticRegion uniqueHgOrdStaticRegion = UniqueRegion.execute(hgOrdStaticRegion);
                hgOrdValueSymbolTable.makeUniqueKey(DynamicRegion.uniqueCounter);

                Pair<Stmt, VarTypeTable> hgOrdUniqueStmtType = attemptHighOrderRegion(c, uniqueHgOrdStaticRegion, hgOrdValueSymbolTable);

                Stmt hgOrdStmt = hgOrdUniqueStmtType.getFirst();
                VarTypeTable hgOrdTypeTable = hgOrdUniqueStmtType.getSecond();

                staticRegion.varTypeTable.mergeTable(hgOrdTypeTable);
                Stmt returnStmt;
                if (c.result.length == 1) {
                    Pair<Stmt, Expression> stmtRetPair = getStmtRetExp(hgOrdStmt);
                    returnStmt = new AssignmentStmt(c.result[0], stmtRetPair.getSecond());
                    return new CompositionStmt(stmtRetPair.getFirst(), returnStmt);
                } else
                    return hgOrdStmt;
            } else
                return new InvokeInstruction(c.getOriginal(), c.result, params);
        } else {
            return new InvokeInstruction(c.getOriginal(), c.result, params);
        }
    }

    /**
     * Attempts to substitute in a high order region.
     * @param c Current invoke instruction
     * @param methodRegion MethodRegion where the substitution is going to be attempted.
     * @param hgOrdValueSymbolTable Value symbol table for te MethodRegion, usually populated with the parameters.
     * @return A pair of substituted statement for the high order region as well as its VarTypeTable.
     */
    private Pair<Stmt, VarTypeTable> attemptHighOrderRegion(InvokeInstruction c,
                                                            StaticRegion methodRegion,
                                                            ValueSymbolTable hgOrdValueSymbolTable) {

        assert (methodRegion.isMethodRegion);

        hgOrdValueSymbolTable.mergeTable(fillValueSymbolTable(ti, methodRegion));
        SubstitutionVisitor visitor = new SubstitutionVisitor(ti, methodRegion, hgOrdValueSymbolTable);
        return new Pair<Stmt, VarTypeTable>((Stmt) methodRegion.staticStmt.accept(visitor), methodRegion.varTypeTable);
    }


    /****************** Methods for inlining method regions ******************/

    /**
     * Iterates over the Stmt to get the return statement seperated out of the reset of the statements.
     *
     * @param stmt A statement that ends with a return expression.
     * @return A pair of Statement and retrun Statment.
     */
    private Pair<Stmt, Expression> getStmtRetExp(Stmt stmt) {
        if (stmt instanceof CompositionStmt) {
            Pair<Stmt, Expression> stmtRetPair = getStmtRetExp(((CompositionStmt) stmt).s2);
            return new Pair(new CompositionStmt(((CompositionStmt) stmt).s1, stmtRetPair.getFirst()), stmtRetPair.getSecond());
        } else {
            if (stmt instanceof ReturnInstruction)
                return new Pair<Stmt, Expression>(SkipStmt.skip, (((ReturnInstruction) stmt).rhs));
            else
                return null;
        }
    }

    /**
     * Attempts to find a mapping MethodRegion.
     * @param c Current invoke instruction.
     * @return A pair of the key and the methodRegion if a matching could be found.
     */
    private Pair<String, StaticRegion> findMethodStaticRegion(InvokeInstruction c) {

        SSAInvokeInstruction instruction = c.getOriginal();
        MethodReference methodReference = instruction.getDeclaredTarget();
        CallSiteReference site = instruction.getCallSite();

        //SH: restricting high order regions to static until we have field references in place.
        String className = methodReference.getDeclaringClass().getName().getClassName().toString();
        Atom methodName = methodReference.getName();
        String methodSignature = methodReference.getSignature();
        methodSignature = methodSignature.substring(methodSignature.indexOf('('));
        String key = CreateStaticRegions.constructMethodIdentifier(className + "." + methodName + methodSignature);
        return new Pair<String, StaticRegion>(key, VeritestingMain.veriRegions.get(key));
    }


    /**
     * Fills out the values of all vars that could be discovered in the region.
     * @param ti Current executing thread.
     * @param staticRegion StaticRegion for which the ValueSymbolTable is going to be created.
     * @return Populated ValueSymbolTable for variables in the static region.
     */
    private static ValueSymbolTable fillValueSymbolTable(ThreadInfo ti, StaticRegion staticRegion) {

        StackFrame sf = ti.getTopFrame();

        ValueSymbolTable valueSymbolTable = new ValueSymbolTable();
        Set<Integer> regionVarSet = staticRegion.varTypeTable.getKeys();

        for (Integer var : regionVarSet) {
            Integer slot = staticRegion.inputTable.lookup(var);
            if ((slot != null) && (!staticRegion.isMethodRegion)) {
                String varType = sf.getLocalVariableType(slot);
                gov.nasa.jpf.symbc.numeric.Expression varValueExp;
                varValueExp = (gov.nasa.jpf.symbc.numeric.Expression) sf.getLocalAttr(slot);
                if (varValueExp == null)
                    try {
                        int varValue = sf.getLocalVariable(slot);
                        varValueExp = createSPFVariableForType(sf, varValue, varType);
                    } catch (StaticRegionException e) {
                        System.out.println(e.getMessage());
                    }
                Expression greenValue = SPFToGreenExpr(varValueExp);
                valueSymbolTable.add(var, greenValue);

            } else { //not a stack slot var, try to check if it is a constant from wala
                SymbolTable symbolTable = staticRegion.ir.getSymbolTable();
                if ((var > -1) && (symbolTable.isConstant(var))) {
                    Expression greenValue = makeConstantFromWala(staticRegion.ir.getSymbolTable(), var);
                    valueSymbolTable.add(var, greenValue);
                }
            }
        }
        return valueSymbolTable;
    }

    /**
     * Executes substitution over a non-method region.
     *
     * @param ti           Thread Information currently running by JPF.
     * @param staticRegion A non-method region that was statically summarized.
     * @return A Dynamic Region that has been substituted by symbolic or concerete values for inputs as well as constants being substituted.
     */

    public static DynamicRegion execute(ThreadInfo ti, StaticRegion staticRegion) {

        ValueSymbolTable valueSymbolTable;

        assert (!staticRegion.isMethodRegion);
        valueSymbolTable = fillValueSymbolTable(ti, staticRegion);

        SubstitutionVisitor visitor = new SubstitutionVisitor(ti, staticRegion, valueSymbolTable);
        Stmt dynStmt = staticRegion.staticStmt.accept(visitor);
        DynamicRegion dynRegion = new DynamicRegion(staticRegion, dynStmt, new HashSet<>());

/*
        System.out.println("\n--------------- SUBSTITUTION TRANSFORMATION ---------------\n");
        System.out.println(StmtPrintVisitor.print(dynRegion.dynStmt));
        dynRegion.slotParamTable.print();
        dynRegion.outputTable.print();
        dynRegion.varTypeTable.print();
*/

        return dynRegion;
    }

}
