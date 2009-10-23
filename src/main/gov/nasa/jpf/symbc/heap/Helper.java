package gov.nasa.jpf.symbc.heap;



import gov.nasa.jpf.jvm.ClassInfo;
import gov.nasa.jpf.jvm.DoubleFieldInfo;
import gov.nasa.jpf.jvm.ElementInfo;
import gov.nasa.jpf.jvm.FieldInfo;
import gov.nasa.jpf.jvm.FloatFieldInfo;
import gov.nasa.jpf.jvm.IntegerFieldInfo;
import gov.nasa.jpf.jvm.LongFieldInfo;
import gov.nasa.jpf.jvm.ReferenceFieldInfo;
import gov.nasa.jpf.jvm.StaticArea;
import gov.nasa.jpf.jvm.StaticElementInfo;
import gov.nasa.jpf.jvm.ThreadInfo;
import gov.nasa.jpf.symbc.bytecode.BytecodeUtils.VarType;
import gov.nasa.jpf.symbc.numeric.Expression;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;
import gov.nasa.jpf.symbc.numeric.SymbolicReal;
import gov.nasa.jpf.symbc.string.StringSymbolic;

public class Helper {

	public static SymbolicInteger SymbolicNull = new SymbolicInteger("SymbolicNull"); // hack for handling static fields

	public static Expression initializeInstanceField(FieldInfo field, ElementInfo eiRef,
			String refChain, String suffix){
		Expression sym_v = null;
		String name ="";

		name = field.getName();
		String fullName = refChain + "." + name + suffix;
		if (field instanceof IntegerFieldInfo || field instanceof LongFieldInfo) {
			if ("boolean".equals(field.getType()))
				//					treat boolean as an integer with range [0,1]
				sym_v = new SymbolicInteger(fullName, 0, 1);
			else
				sym_v = new SymbolicInteger(fullName);
		} else if (field instanceof FloatFieldInfo || field instanceof DoubleFieldInfo) {
			sym_v = new SymbolicReal(fullName);
		} else if (field instanceof ReferenceFieldInfo){
			if (field.getType().equals("java.lang.String"))
				sym_v = new StringSymbolic(fullName);
			else
				sym_v = new SymbolicInteger(fullName);
		}
		eiRef.setFieldAttr(field, sym_v);
		return sym_v;
	}

	public static void initializeInstanceFields(FieldInfo[] fields, ElementInfo eiRef,
			String refChain){
		for (int i=0; i<fields.length;i++)
			initializeInstanceField(fields[i], eiRef, refChain, "");
	}

	public static Expression initializeStaticField(FieldInfo staticField, ClassInfo ci,
			ThreadInfo ti, String suffix){

		Expression sym_v = null;
		String name ="";

		name = staticField.getName();
		String fullName = ci.getName() + "." + name + suffix;// + "_init";
		if (staticField instanceof IntegerFieldInfo || staticField instanceof LongFieldInfo) {
			if ("boolean".equals(staticField.getType()))
				//						treat boolean as an integer with range [0,1]
				sym_v = new SymbolicInteger(fullName, 0, 1);
			else
				sym_v = new SymbolicInteger(fullName);
		} else if (staticField instanceof FloatFieldInfo
				|| staticField instanceof DoubleFieldInfo) {
			sym_v = new SymbolicReal(fullName);
		}else if (staticField instanceof ReferenceFieldInfo){
			if (staticField.getType().equals("java.lang.String"))
				sym_v = new StringSymbolic(fullName);
			else
				sym_v = new SymbolicInteger(fullName);
		}
		StaticElementInfo sei = ci.getStaticElementInfo();
		if (sei == null)
			StaticArea.getStaticArea().addClass(ci, ti);
		if (sei.getFieldAttr(staticField) == null)
			sei.setFieldAttr(staticField, sym_v);
		return sym_v;
	}

	public static void initializeStaticFields(FieldInfo[] staticFields, ClassInfo ci,
			ThreadInfo ti){

		if (staticFields.length > 0) {
			for (int i = 0; i < staticFields.length; i++)
				initializeStaticField(staticFields[i], ci, ti, "");
		}
	}
}
