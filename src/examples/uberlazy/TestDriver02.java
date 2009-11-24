package uberlazy;

/* A mix of concrete and symbolic values in the fields */

public class TestDriver02 {
	
	Node n;
	Node m;
	
	public void run() {
		if(m != null) {
			m.elem = 5;
			// when invoked from this location both the
			// print statements should be displayed. 
			differentField();
		} else{
			// when called from here the "aliasing" print 
			// statement should not be triggered. 
			differentField();
		}
	}
	
	public void differentField() {
		if(n != null) {
			// when a primitive field reference is read	
			// and it differs in the value then the partition
			// function separates the ones that are different
			if(n.elem == 5) { 
				System.out.println("the partition function accounts for aliasing");
			} else {
				System.out.println("all other elements in the partition function");
			}
		}
	}
	
	public static void main(String[] args) {
		TestDriver02 tt = new TestDriver02();
		tt.run();
	}
	
}