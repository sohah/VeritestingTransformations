package rjc;

import java.io.*;
import java.util.ArrayList;

public class RJCMain {
	protected rjc controller;
	protected String filename1, filename2; // 2 CSV files for this example

	public RJCMain() {
		this.controller = new rjc();
		this.controller.Init2();
	}

	public RJCMain(String filename1, String filename2) {
		this();
		this.filename1 = filename1;
		this.filename2 = filename2;
	}

	public void DoSim() {

		ArrayList<ArrayList<String>> cmdInputs = new ArrayList<ArrayList<String>>();
		ArrayList<ArrayList<String>> measInputs = new ArrayList<ArrayList<String>>();
		ArrayList<ArrayList<Double>> cmdVars = new ArrayList<ArrayList<Double>>();
		ArrayList<ArrayList<Double>> measVars = new ArrayList<ArrayList<Double>>();

		try {
			File file1 = new File(this.filename1);
			File file2 = new File(this.filename2);

			FileInputStream fis1 = new FileInputStream(file1);
			FileInputStream fis2 = new FileInputStream(file2);

			BufferedReader br1 = new BufferedReader(new InputStreamReader(fis1));
			BufferedReader br2 = new BufferedReader(new InputStreamReader(fis2));
			String strLine;

			// Read File Line By Line
			while ((strLine = br1.readLine()) != null) {
				if (!strLine.isEmpty()) {
					String[] inputs = strLine.split(",");
					ArrayList<String> line = new ArrayList<String>();
					ArrayList<Double> dubLine = new ArrayList<Double>();
					for (int ix = 0; ix < inputs.length; ix++) {
						line.add(inputs[ix]);
						dubLine.add(Double.parseDouble(inputs[ix]));
					}
					cmdInputs.add(line);
					cmdVars.add(dubLine);
				}
			}

			while ((strLine = br2.readLine()) != null) {
				if (!strLine.isEmpty()) {
					String[] inputs = strLine.split(",");
					ArrayList<String> line = new ArrayList<String>();
					ArrayList<Double> dubLine = new ArrayList<Double>();
					for (int ix = 0; ix < inputs.length; ix++) {
						line.add(inputs[ix]);
						dubLine.add(Double.parseDouble(inputs[ix]));
					}
					measInputs.add(line);
					measVars.add(dubLine);
				}
			}

			fis1.close();
			fis2.close();

			BufferedWriter out = new BufferedWriter(new FileWriter("JavaOutput.csv")); // Write the second output to a file

			for (int i = 0; i < cmdInputs.size() && i < measInputs.size(); i++) {
				ArrayList<Double> currCmd = cmdVars.get(i);
				ArrayList<Double> currMeas = measVars.get(i);
				// For now assume they are the correct size
				double[] output1 = new double[1];
				double[] output2 = new double[2];
				double[] input1 = new double[3];
				double[] input2 = new double[3];
				for (int j = 0; j < 3; j++) {
					input1[j] = currCmd.get(j + 1); // Throw away the time stamp
					input2[j] = currMeas.get(j + 1); // Throw away the time stamp
				}
				this.controller.Main0(input1, input2, output1, output2);

				System.out.println("Output 1 (yaw jets)   : " + output1[0]);
				System.out.println("Output 2 (pitch jets) : " + output2[0] + ", " + output2[1]);
				out.write("" + currCmd.get(0) + "," + output2[0] + "," + output2[1] + "\n");
			}

			out.close();

		}
		catch (Exception e) {
			System.out.println(e.getMessage());
		}
	}

	// Symbolic pathfinder cannot handle arrays, so use this method if you want to run the process symbolically
	public void DoSimSymbolic() {
		double[] out1 = new double[1];
		double[] out2 = new double[2];

		// sequences up to length 5
		for (int i = 0; i < 5; i++) {
			System.out.println("i "+i);
			out1 = new double[1];
			out2 = new double[2];
			this.controller.MainSymbolic(0, 0, 0, 0, 0, 0, out1, out2);
		}
	}

	// run the test with auto-generated values
	public void DoSimTest() {
		double[] out1 = new double[1];
		double[] out2 = new double[2];
//		this.controller.MainSymbolic(99.6281945338004,66.51337872672673,-40.88166076866777,92.39235522972619,67.12570469421118,67.17120847166747,out1,out2);
//		this.controller.MainSymbolic(58.62875465816707,-35.544716036917656,-18.897292236180018,-0.005659692497617108,-18.808794885386014,-3.0431933547029333,out1,out2);
//		this.controller.MainSymbolic(-34.44755466215843,78.17363037150778,93.349422458694,-35.21652615994913,-37.734474929333686,-6.64618601916751,out1,out2);
//		this.controller.MainSymbolic(-42.07702985547167,68.40098299452964,70.81143363726822,-99.99999990000003,-27.603501953651786,-27.048812327683102,out1,out2);
//		this.controller.MainSymbolic(-3.163929986924374,92.70154403880161,77.0481169935139,55.64784881322824,-23.86510538845049,97.4428559519558,out1,out2);

		this.controller.MainSymbolic(1,1,1,1,1,1,out1,out2);
		this.controller.MainSymbolic(1,1,1,1,1,1,out1,out2);
//		this.controller.MainSymbolic(1,1,1,1,1,1,out1,out2);
//		this.controller.MainSymbolic(1,1,1,1,1,1,out1,out2);
//		this.controller.MainSymbolic(1,1,1,1,1,1,out1,out2);
	}


	public static void main(String[] args) {
		RJCMain rjcmain;
		if (args.length < 2) { // Run symbolically if no args
			rjcmain = new RJCMain();
			rjcmain.DoSimSymbolic();
		}
		else {
			//rjcmain = new RJCMain(args[0], args[1]);
			//rjcmain.DoSim();
			System.out.println("Running tests!");
			rjcmain = new RJCMain();
			rjcmain.DoSimTest();
		}
	}
}
