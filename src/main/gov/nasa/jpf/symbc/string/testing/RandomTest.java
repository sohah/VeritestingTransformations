package gov.nasa.jpf.symbc.string.testing;

import java.util.List;
import java.util.Random;

import gov.nasa.jpf.Config;
import gov.nasa.jpf.symbc.SymbolicInstructionFactory;
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.numeric.SymbolicConstraintsGeneral;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;
import gov.nasa.jpf.symbc.string.SymbolicIntegerGenerator;
import gov.nasa.jpf.symbc.string.graph.EdgeContains;
import gov.nasa.jpf.symbc.string.graph.EdgeEndsWith;
import gov.nasa.jpf.symbc.string.graph.EdgeEqual;
import gov.nasa.jpf.symbc.string.graph.EdgeNotContains;
import gov.nasa.jpf.symbc.string.graph.EdgeNotEndsWith;
import gov.nasa.jpf.symbc.string.graph.EdgeNotEqual;
import gov.nasa.jpf.symbc.string.graph.EdgeNotStartsWith;
import gov.nasa.jpf.symbc.string.graph.EdgeStartsWith;
import gov.nasa.jpf.symbc.string.graph.PreProcessGraph;
import gov.nasa.jpf.symbc.string.graph.StringGraph;
import gov.nasa.jpf.symbc.string.graph.Vertex;
import gov.nasa.jpf.symbc.string.translate.BVVar;
import gov.nasa.jpf.symbc.string.translate.TranslateToAutomata;
import gov.nasa.jpf.symbc.string.translate.TranslateToZ3;
import gov.nasa.jpf.symbc.string.translate.TranslateToZ3Inc;

public class RandomTest {
	
	static int totalWeight;
	static SymbolicIntegerGenerator sig;
	static Random random;
	static int counter;
	static PathCondition pc;
	
	private static final String Z3_Inc = "Z3 Inc";
	private static final String Z3 = "Z3";
	private static final String Automata = "Automata";
	
	public static void main (String [] args) {
		setUpJPF();
		Profile p = Profile.NewProfile();
		p.amountOfStringCons = 5;
		p.stringConsMaxLength = 5;
		p.amountOfStringVar = 2;
		p.amountOfEdges = 5;
		
		p.listOfEdgesToBeUsed = Profile.smallSetOfEdges();
		
		//args = new String[]{"4482676770472428340"};
		//args = new String[]{"7463434583100419681"};
		//args = new String[]{"6195941135273736924"};
		//args = new String[]{"-5452898171472999736"};
		//args = new String[]{"-8789835043277711195"};
		//args = new String[]{"-8333472512654717307"};
		//TODO: 2797260435590869202
		if (args.length == 0) {
			for (int i = 0; i < 100; i++) {
				random = new Random();
				long seed = random.nextLong();
				go (p, seed, Z3_Inc);
				go (p, seed, Automata);
			}
		}
		else {
			long seed = Long.parseLong(args[0]);
			random = new Random();
			go (p, seed, Z3_Inc);
		}
	}
	
	public static void go (Profile p, long seed, String Solver) {
		StringGraph sg = generateRandomStringGraph (p, seed);
		System.out.println(sg.toDot());
		boolean result = PreProcessGraph.preprocess(sg, pc);
		//System.out.println(sg.toDot());
		//System.out.println(pc.header);
		System.out.println("Preprocessor " + result);
		if (result == false) {}
		else {
			long time = System.currentTimeMillis();
			if (Solver.equals (Z3_Inc)) {
				TranslateToZ3Inc.isSat(sg, pc);
			}
			else if (Solver.equals(Automata)) {
				TranslateToAutomata.isSat(sg, pc);
			}
			long dur = System.currentTimeMillis() - time;
			System.out.println("[output] " + Solver + ": " + dur);
		}
	}
	
	public static void setUpJPF () {
		Config cfg = new Config(new String[]{""});
		new SymbolicInstructionFactory(cfg);
	}
	
	public static StringGraph generateRandomStringGraph (Profile p, long seed) {
		StringGraph result = new StringGraph();
		pc = new PathCondition();
		System.out.println("Random seed: " + seed);
		random.setSeed(seed);
		counter = 0;
		
		totalWeight = 0;
		for (int i = 0; i < p.listOfEdgesToBeUsed.length; i++) {
			totalWeight = totalWeight + p.listOfEdgesToBeUsed[i];
		}
		
		sig = new SymbolicIntegerGenerator();
		char character = 'a';
		
		for (int i = 0; i < p.amountOfStringVar; i++) {
			result.addVertex(new Vertex("SYM_" + String.valueOf(character), sig));
			character = (char) ((int) character + 1);
		}
		
		for (int i = 0; i < p.amountOfStringCons; i++) {
			String name = getRandomConstantString (random.nextInt(p.stringConsMaxLength) + 1);
			result.addVertex(new Vertex("CONST_" + name, name, true));
		}
		
		for (int i = 0; i < p.amountOfEdges; i++ ) {
			double ran = random.nextDouble();
			ran = ran * totalWeight;
			ran = Math.round (ran);
			int index = getIndex ((int) ran, p.listOfEdgesToBeUsed);
			switch (index) {
			case 0:
				//EdgeCharAt
				throw new RuntimeException ("Not implemented yet");
			case 1:
				//EdgeConcat
				throw new RuntimeException ("Not implemented yet");
			case 2:
				//EdgeContains
				handleEdgeContains (result);
				break;
			case 3:
				//EdgeEndsWith
				handleEdgeEndsWith (result);
				break;
			case 4:
				//EdgeEqual
				handleEdgeEqual (result);
				break;
			case 5:
				//EdgeIndexOf
				throw new RuntimeException ("Not implemented yet");
			case 6:
				//EdgeIndexOf2
				throw new RuntimeException ("Not implemented yet");
			case 7:
				//EdgeIndexOfChar
				throw new RuntimeException ("Not implemented yet");
			case 8:
				//EdgeIndexOfChar2
				throw new RuntimeException ("Not implemented yet");
			case 9:
				//EdgeLastIndexOf
				throw new RuntimeException ("Not implemented yet");
			case 10:
				//EdgeLastIndexOf2
				throw new RuntimeException ("Not implemented yet");
			case 11:
				//EdgeLastIndexOfChar
				throw new RuntimeException ("Not implemented yet");
			case 12:
				//EdgeLastIndexOfChar2
				throw new RuntimeException ("Not implemented yet");
			case 13:
				//EdgeNotContains
				handleEdgeNotContains (result);
				break;
			case 14:
				//EdgeNotEndsWith
				handleEdgeNotEndsWith (result);
				break;
			case 15:
				//EdgeNotEquals
				handleEdgeNotEquals (result);
				break;
			case 16:
				//EdgeNotStartsWith
				handleEdgeNotStartsWith (result);
				break;
			case 17:
				//EdgeReplaceCharChar
				throw new RuntimeException ("Not implemented yet");
			case 18:
				//EdgeStartsWith
				handleEdgeStartsWith (result);
				break;
			case 19:
				//EdgeSubstring1Equal
				throw new RuntimeException ("Not implemented yet");
			case 20:
				//EdgeSubstring2Equal
				throw new RuntimeException ("Not implemented yet");
			case 21:
				//EdgeTrimEqual
				throw new RuntimeException ("Not implemented yet");
			}
		}
		
		return result;
	}
	
	private static void handleEdgeStartsWith (StringGraph result) {
		Vertex v1 = selectRandomVertex(result);
		Vertex v2 = selectRandomVertex(result);
		while (v1.equals(v2) || (v1.isConstant() && v2.isConstant())) {
			v1 = selectRandomVertex(result);
			v2 = selectRandomVertex(result);
		}
		EdgeStartsWith edge = new EdgeStartsWith("EdgeStartsWith_" + getCounter(), v1, v2);
		result.addEdge(v1, v2, edge);
	}
		
	private static void handleEdgeNotEquals (StringGraph result) {
		Vertex v1 = selectRandomVertex(result);
		Vertex v2 = selectRandomVertex(result);
		while (v1.equals(v2) || (v1.isConstant() && v2.isConstant())) {
			v1 = selectRandomVertex(result);
			v2 = selectRandomVertex(result);
		}
		//TODO: Investigate
		if (v2.isConstant()) {
			pc._addDet(Comparator.GE, v1.getSymbolicLength(), v2.getLength());
		}
		EdgeNotEqual edge = new EdgeNotEqual("EdgeNotEqual_" + getCounter(), v1, v2);
		result.addEdge(v1, v2, edge);
	}
	
	private static void handleEdgeNotStartsWith (StringGraph result) {
		Vertex v1 = selectRandomVertex(result);
		Vertex v2 = selectRandomVertex(result);
		while (v1.equals(v2) || (v1.isConstant() && v2.isConstant())) {
			v1 = selectRandomVertex(result);
			v2 = selectRandomVertex(result);
		}
		//TODO: Investigate
		if (v2.isConstant()) {
			pc._addDet(Comparator.GE, v1.getSymbolicLength(), v2.getLength());
		}
		EdgeNotStartsWith edge = new EdgeNotStartsWith("EdgeNotStartsWith_" + getCounter(), v1, v2);
		result.addEdge(v1, v2, edge);
	}
	
	private static void handleEdgeNotEndsWith (StringGraph result) {
		Vertex v1 = selectRandomVertex(result);
		Vertex v2 = selectRandomVertex(result);
		while (v1.equals(v2) || (v1.isConstant() && v2.isConstant())) {
			v1 = selectRandomVertex(result);
			v2 = selectRandomVertex(result);
		}
		//TODO: Investigate
		if (v2.isConstant()) {
			pc._addDet(Comparator.GE, v1.getSymbolicLength(), v2.getLength());
		}
		EdgeNotEndsWith edge = new EdgeNotEndsWith("EdgeNotEndsWith_" + getCounter(), v1, v2);
		result.addEdge(v1, v2, edge);
	}
	
	private static void handleEdgeNotContains (StringGraph result) {
		Vertex v1 = selectRandomVertex(result);
		Vertex v2 = selectRandomVertex(result);
		while (v1.equals(v2) || (v1.isConstant() && v2.isConstant())) {
			v1 = selectRandomVertex(result);
			v2 = selectRandomVertex(result);
		}
		EdgeNotContains edge = new EdgeNotContains("EdgeNotContains_" + getCounter(), v1, v2);
		//TODO: Investigate
		if (v2.isConstant()) {
			pc._addDet(Comparator.GE, v1.getSymbolicLength(), v2.getLength());
		}
		result.addEdge(v1, v2, edge);
	}
	
	private static void handleEdgeEqual (StringGraph result) {
		Vertex v1 = selectRandomVertex(result);
		Vertex v2 = selectRandomVertex(result);
		while (v1.equals(v2) || (v1.isConstant() && v2.isConstant())) {
			v1 = selectRandomVertex(result);
			v2 = selectRandomVertex(result);
		}
		EdgeEqual edge = new EdgeEqual("EdgeEqual_" + getCounter(), v1, v2);
		result.addEdge(v1, v2, edge);
	}
	
	private static void handleEdgeEndsWith (StringGraph result) {
		Vertex v1 = selectRandomVertex(result);
		Vertex v2 = selectRandomVertex(result);
		while (v1.equals(v2) || (v1.isConstant() && v2.isConstant())) {
			v1 = selectRandomVertex(result);
			v2 = selectRandomVertex(result);
		}
		EdgeEndsWith edge = new EdgeEndsWith("EdgeEndsWith_" + getCounter(), v1, v2);
		result.addEdge(v1, v2, edge);
	}
	
	private static void handleEdgeContains (StringGraph result) {
		Vertex v1 = selectRandomVertex(result);
		Vertex v2 = selectRandomVertex(result);
		while (v1.equals(v2) || (v1.isConstant() && v2.isConstant())) {
			v1 = selectRandomVertex(result);
			v2 = selectRandomVertex(result);
		}
		EdgeContains edge = new EdgeContains("EdgeContains_" + getCounter(), v1, v2);
		result.addEdge(v1, v2, edge);
	}
	
	private static int getCounter () {
		int oldcount = counter;
		counter++;
		return oldcount;
	}
	
	private static Vertex selectRandomVertex (StringGraph g) {
		List<Vertex> vertecis = g.getVertices();
		int ranIndex = random.nextInt(vertecis.size());
		return vertecis.get(ranIndex);
	}
	
	private static String getRandomConstantString (int length) {
		StringBuilder sb = new StringBuilder();
		for (int i = 0; i < length; i++) {
			char character = (char) (random.nextInt(94) + 32);
			sb.append (character);
		}
		return sb.toString();
	}
	
	private static int getIndex (int num, int [] list) {
		int runningTotal = 0;
		for (int i = 0; i < list.length; i++) {
			runningTotal = runningTotal + list[i];
			if (runningTotal > num) {
				return i;
			}
		}
		for (int i = list.length - 1; i >= 0; i--) {
			if (list[i] > 0) {
				return i;
			}
		}
		return -1;
	}
}
