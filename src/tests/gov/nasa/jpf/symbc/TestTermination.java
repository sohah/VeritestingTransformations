package gov.nasa.jpf.symbc;

public class TestTermination {
	static void test(int i, int j, int k) {
		//while (i <= 100 && j <= k) {
		if(i <=100 && j <=k) {
			int oldi = i;
			int oldj = j;
			int oldk = k;

			i = j;
			j = i + 1;
			k = k-1;
			if(oldi > i && oldk-oldj <= k-j)
				assert false;
			else
				System.out.println("here");
		}
	}
	
	public static void main(String[] args) {
		test (0,0,0);
	}

}
