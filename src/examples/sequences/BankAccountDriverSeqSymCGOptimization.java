package sequences;


import gov.nasa.jpf.vm.Verify;
import gov.nasa.jpf.symbc.Debug;
import gov.nasa.jpf.symbc.Preconditions;


public class BankAccountDriverSeqSymCGOptimization {

	public static void testDriver(int length){
		BankAccount b = new BankAccount(0);
		for (int i=0; i<length; i++){
			Verify.beginAtomic();
			
			if(flag(true) == 1) {
				b.deposit(10);
				if(flag(true) != 1) {
					int a = 42;
				}
				
			} else if(flag(true) == 0) {
				b.withdraw(1);
				if(flag(true) != 0) {
					int a = 42;
				}
			}
			Verify.endAtomic();
		}
	}
	
	public static int flag(boolean x) {
	if (x)
		return 1;
	else
		return 0;
	}

	public static void main(String[] args){
		testDriver(2);
		Debug.printPC("Path Condition: ");
		System.out.println();
	}
}
