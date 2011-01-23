package gov.nasa.jpf.symbc.string.translate;

import java.util.HashMap;
import java.util.Map;

public class BVVar implements BVExpr{
	String name;
	int size;
	
	static Map<String, Character> map;
	static Map<Character, String> reverseMap;
	static char startChar;
	
	public BVVar(String name, int size) {
		this.name = name;
		this.size = size;
	}
	
	public String toString () {
		return name;
	}
	
	public String toSMTLibDec () {
		char currentChar;
		if (map == null) {
			map = new HashMap<String, Character>();
			reverseMap = new HashMap<Character, String>();
			startChar = 'a';
			currentChar = 'a';
			map.put(name, startChar);
			reverseMap.put(startChar, name);
			startChar++;
		}
		else if (map.get(name) != null) {
			currentChar = map.get(name);
		}
		else {
			map.put(name, startChar);
			reverseMap.put(startChar, name);
			currentChar = startChar;
			startChar++;
		}
		
		StringBuilder sb = new StringBuilder();
		
		sb.append ("(declare-fun "); 
		sb.append (currentChar);		
		sb.append (" () (_ BitVec ");
		sb.append (size);
		sb.append ("))");
		
		return sb.toString();
	}
	
	public String toSMTLib () {
		return String.valueOf(map.get(name));
	}
}
