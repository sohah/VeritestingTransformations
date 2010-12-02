package gov.nasa.jpf.symbc.concolic;


import gov.nasa.jpf.Config;
import gov.nasa.jpf.JPF;
import gov.nasa.jpf.PropertyListenerAdapter;
import gov.nasa.jpf.jvm.AnnotationInfo;
import gov.nasa.jpf.jvm.JVM;
import gov.nasa.jpf.jvm.MethodInfo;
import gov.nasa.jpf.jvm.StackFrame;
import gov.nasa.jpf.jvm.ThreadInfo;
import gov.nasa.jpf.jvm.bytecode.Instruction;
import gov.nasa.jpf.jvm.bytecode.InvokeInstruction;
import gov.nasa.jpf.report.ConsolePublisher;
import gov.nasa.jpf.symbc.numeric.Expression;
import gov.nasa.jpf.symbc.numeric.RealConstant;
import gov.nasa.jpf.symbc.numeric.RealExpression;

public class ConcreteExecutionListener extends PropertyListenerAdapter {

	Config config;
	public static boolean debug = false;
	long ret;
	Object resultAttr; 
	
	public ConcreteExecutionListener(Config conf, JPF jpf) {
		jpf.addPublisherExtension(ConsolePublisher.class, this);
		this.config = conf;
	}
	
	public void instructionExecuted(JVM vm) {
		Instruction lastInsn =  vm.getLastInstruction();
		MethodInfo mi = vm.getCurrentThread().getMethod();
		if(lastInsn != null && lastInsn instanceof InvokeInstruction) {
			boolean foundAnote = checkConcreteAnnotation(mi);
			if(foundAnote) {
				
				System.out.println(lastInsn.getSourceLine() + "srcLine");
				ThreadInfo ti = vm.getCurrentThread();
				//ti.setReturnValue(0);
				
				StackFrame sf = ti.popFrame();
				generateFunctionExpression(mi, (InvokeInstruction) lastInsn, ti);
				ti.removeArguments(mi);
				ti.longPush(ret);
				ti.setLongOperandAttr(resultAttr);
				
				Instruction nextIns = sf.getPC().getNext();
				System.out.println(nextIns.getSourceLine());
				
				
				
			    vm.getCurrentThread().skipInstruction();
			    vm.getCurrentThread().setNextPC(nextIns);
			
				
			}
		}
	}

	private boolean checkConcreteAnnotation(MethodInfo mi) {
		AnnotationInfo[] ai = mi.getAnnotations();
		if(ai == null || ai.length == 0)  return false;
		for(int aIndex = 0; aIndex < ai.length; aIndex++) {
			AnnotationInfo annotation = ai[aIndex];
			if(annotation.getName().equals
							("gov.nasa.jpf.symbc.Concrete")) {
				if(annotation.valueAsString().
									equalsIgnoreCase("true"))
					return true;
				else 
					return false;
			}
		}
		return false;
	}
	
	private void generateFunctionExpression(MethodInfo mi, InvokeInstruction ivk,
			ThreadInfo ti){
		
		Object [] attrs = ivk.getArgumentAttrs(ti);
		Object [] values = ivk.getArgumentValues(ti);
		String [] types = mi.getArgumentTypeNames();
		
		assert (attrs != null);
		
		assert (attrs.length == values.length && 
						values.length == types.length);
		int size = attrs.length;
		
		Class<?>[] args_type = new Class<?> [size];
		Expression[] sym_args = new Expression[size];
		
		for(int argIndex = 0; argIndex < size; argIndex++) {
			Object attribute = attrs[argIndex];
			if(attribute == null) {
				//create a new constant
				// for now we assume you can only pass doubles
				sym_args[argIndex] = new RealConstant(Double.parseDouble
									(values[argIndex].toString()));
			} else {
				sym_args[argIndex] = (Expression) attribute;
			}
			args_type[argIndex] = Double.TYPE;
		}
		System.out.println("In the generate function expression" + mi.getClassName());
		
		FunctionExpression result = new FunctionExpression(
				  mi.getClassName(),
				  mi.getName(), args_type, sym_args);
		System.out.println("result is :" + result.toString());
		ret = 0;
		resultAttr = result;
	}
	
}