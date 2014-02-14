import gov.nasa.jpf.symbc.Debug;


public class TestZ3 {
	public static void test(int x, int y) {
		if(x-y<=y)
			System.out.println("eq "+Debug.getSolvedPC());
		else
			System.out.println("neq "+Debug.getSolvedPC());
	}
	public static void main(String[] args) {
		test(0,0);
	}
}
