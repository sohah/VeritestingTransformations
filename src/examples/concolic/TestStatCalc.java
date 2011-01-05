package concolic;

public class TestStatCalc {
	
	public void run(int val) {
		
		System.out.println("adding value");
		StatCalculator.addValue(val);
		//stat.addValue(val);
		//stat.addValue(val);
		if(StatCalculator.getMedian().intValue() == 16.00) {
			System.out.println("median value is 16");
		} else {
			System.out.println("median value is not 16");
		}
		if(StatCalculator.getStandardDeviation(StatCalculator.getMean()) == 0.10) {
			System.out.println("std deviation is .10");
		} else {
			System.out.println("std deviation not found");
		}
	}
	
	public static void main(String[] args) {
		TestStatCalc stat = new TestStatCalc();
		stat.run(0);
		
	}
	
}