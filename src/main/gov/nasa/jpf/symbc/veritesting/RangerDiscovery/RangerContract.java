package gov.nasa.jpf.symbc.veritesting.RangerDiscovery;

import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import gov.nasa.jpf.symbc.veritesting.ast.def.FieldRefVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.vm.ElementInfo;
import gov.nasa.jpf.vm.FieldInfo;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;
import za.ac.sun.cs.green.expr.Expression;

import java.io.BufferedWriter;
import java.io.FileOutputStream;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;

public class RangerContract {

    /* This map is used to populate the spfQuery for z3, for later mainpulation. */
    public static ArrayList<Pair> z3QuerySet = new ArrayList<>();



    public static ArrayList<String> freeInput = new ArrayList<>();
    public static ArrayList<String> stateInput = new ArrayList<>();
    public static ArrayList<String> stateOutput = new ArrayList<>();
    public static ArrayList<String> intermediateVar = new ArrayList<>();

    public static DynamicRegion dynRegion;


    public static void discoverRangerVars() {
        collectOutput();
    }

    private static void collectOutput() {
        try {
            for (Iterator<FieldRefVarExpr> fieldRefItr = dynRegion.psm.getUniqueFieldAccess().iterator();
                 ((Iterator) fieldRefItr).hasNext(); ) {

                FieldRefVarExpr entry = fieldRefItr.next();
                stateOutput.add(entry.toString());
                //rangerTypeTable.put(entry.toString(), dynRegion.fieldRefTypeTable.lookup(entry));
            }
        } catch (StaticRegionException e) {
            System.out.println("error while collecting output of field for region discovery.");
        }
        Collections.sort(stateOutput);
    }


    public static void collectInput(ThreadInfo ti, Expression[] params, String currClassName, DynamicRegion dynRegion) {
        StackFrame sf = ti.getTopFrame();
        collectParameterInput(sf, params, dynRegion);
        collectStateInput(ti, currClassName);
    }

    private static void collectStateInput(ThreadInfo ti, String currClassName) {
        ElementInfo objRef = null;
        Iterator<ElementInfo> heapItr = ti.getHeap().iterator();

        while (objRef == null & heapItr.hasNext()) {
            ElementInfo tempObj = heapItr.next();
            if (("L" + tempObj.getClassInfo().getName() + ";").equals(currClassName))
                objRef = tempObj;
        }


        if (objRef != null) {
            FieldInfo[] declaredFields = objRef.getClassInfo().getDeclaredInstanceFields();
            for (int i = 0; i < declaredFields.length; i++) {
                Object fieldSym = objRef.getFields().getFieldAttr(i);
                //if the field has a symbolic value then this is a symbolic state of the object that should be considered as an input
                if (fieldSym != null) {
                    stateInput.add(fieldSym.toString());
                }
            }
        }
        Collections.sort(stateInput);
    }


    private static void collectParameterInput(StackFrame sf, Expression[] params, DynamicRegion dynRegion) {
        // for now dealing with just a single input method, to generalize I need to add this into a for loop
        int[] slot = (int[]) dynRegion.slotParamTable.lookup(params[1]);

        if (slot != null && slot.length > 0) {
            gov.nasa.jpf.symbc.numeric.Expression sym =
                    (gov.nasa.jpf.symbc.numeric.Expression) sf.getLocalAttr(slot[0]);
            if (sym != null) {
                freeInput.add(sym.toString());
            }
        }
    }

    public static void dumpInputOutput(String fileName) {
        try (Writer writer = new BufferedWriter(new OutputStreamWriter(
                new FileOutputStream(fileName + "FreeIN"), "utf-8"))) {
            writer.write(DiscoveryUtility.writeArrayList(freeInput));
        } catch (Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Error : " + e);
        }

        try (Writer writer = new BufferedWriter(new OutputStreamWriter(
                new FileOutputStream(fileName + "StateIN"), "utf-8"))) {
            writer.write(DiscoveryUtility.writeArrayList(stateInput));
        } catch (Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Error : " + e);
        }

        try (Writer writer = new BufferedWriter(new OutputStreamWriter(
                new FileOutputStream(fileName + "OUT"), "utf-8"))) {
            writer.write(DiscoveryUtility.writeArrayList(stateOutput));
        } catch (Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Error : " + e);
        }

    }


}
