package gov.nasa.jpf.symbc.string.testing;

import gov.nasa.jpf.symbc.string.graph.Edge;
import gov.nasa.jpf.symbc.string.graph.EdgeCharAt;

import java.util.ArrayList;
import java.util.List;

public class Profile {
	int amountOfStringVar = 2;
	int amountOfStringCons = 5;
	int amountOfEdges = 10;
	
	int[] listOfEdgesToBeUsed = defaultSetOfEdges();
	int stringConsMaxLength = 5;
	
	public static Profile NewProfile () {
		return new Profile();
	}
	
	public static int[] defaultSetOfEdges () {
		int[] result = new int [22];
		for (int i = 0; i < result.length; i++) {
			result[i] = 1;
		}
		return result;
	}
	
	public static int[] smallSetOfEdges () {
		int[] result = new int [22];
		result[2] = 1;
		result[3] = 1;
		result[4] = 1;
		result[13] = 1;
		result[14] = 1;
		result[15] = 1;
		result[16] = 1;
		result[18] = 1;
		return result;
	}
}
