import java.util.*;
import soot.G;
import java.io.*;

class LocalVarsTable {
  String className;
  String methodName;
  HashMap<String, Integer> varsMap;
  HashSet<String> usedLocalVars, intermediateVars;
	HashMap<Integer, Integer> ifToSetup;
  LocalVarsTable(String cN, String mN) {
    varsMap = new HashMap<String, Integer> ();
		intermediateVars = new HashSet<String> ();
    usedLocalVars = new HashSet<String> ();
		ifToSetup = new HashMap<Integer, Integer> ();
    className = cN;
    methodName = mN;
		String prevStr="", prevprevStr="";
    try {
      Runtime rt = Runtime.getRuntime();
      String[] commands = {"javap", "-c", "-l", className};
      Process proc = rt.exec(commands);
      
      BufferedReader stdInput = new BufferedReader( 
                     new InputStreamReader(proc.getInputStream()));
      
      BufferedReader stdError = new BufferedReader(
                     new InputStreamReader(proc.getErrorStream()));
      
      // read the output from the command
      // G.v().out.println("Here is the standard output of the command (for " + className + ") :");
      String s = null;
      boolean methodOfInterest = false;
      boolean mOIVarTable = false;
      while ((s = stdInput.readLine()) != null) {
        if(mOIVarTable && s.length() == 0) {
          mOIVarTable = methodOfInterest = false;
        }
        // if(methodOfInterest) G.v().out.println(s+" " + s.contains("if_"));
        if(s.contains(methodName+"(")) methodOfInterest = true;
        if(methodOfInterest) 
          if(s.contains("LocalVariableTable")) mOIVarTable = true;
        if(mOIVarTable) {
          String[] tokens = s.split("[ ]+");
          // G.v().out.println("tokens.length = " + tokens.length);
          // if(tokens.length == 6)
          //   G.v().out.println(tokens[0]+","+tokens[1]+","+tokens[2]+","+tokens[3]+","+tokens[4]+","+tokens[5]);
          if(tokens.length != 6) continue;
          int slot = -1;
          String name = null;
          try {
            slot = Integer.parseInt(tokens[3]);
            name = tokens[4];
          } catch (Exception e) { }
          if(name != null && slot != -1) {
            varsMap.put(name, slot);
            G.v().out.println("mapped " + name + " to slot = " + slot);
          }
        }
	if(methodOfInterest && s.contains("if_")) {
	  // assume setup instruction is previous-previous from current
	  int start = getOffsetFromLine(s), end = getOffsetFromLine(prevprevStr);
	  ifToSetup.put(start, end);
	  // System.out.println("Adding ("+start+", "+end+") to ifToSetup");
	}
	if(methodOfInterest) {
	  prevprevStr = prevStr;
	  prevStr = s;
	}
      }
      
      // read any errors from the attempted command
      // G.v().out.println("Here is the standard error of the command (if any):\n");
      // while ((s = stdError.readLine()) != null) {
      //   G.v().out.println(s);
      // }
    } catch (IOException i) { G.v().out.println("caught exception " + i); }
  }
  public boolean isLocalVariable(String varName) {
    return varsMap.containsKey(varName);
  }
  public int getLocalVarSlot(String varName) {
		if(isLocalVariable(varName)) return varsMap.get(varName);
		else return -1;
  }
  public void addUsedLocalVar(String varName) { 
    usedLocalVars.add(varName); 
    return;
  }
  public void addIntermediateVar(String varName) { 
    intermediateVars.add(varName); 
    return;
  }
	public void resetUsedLocalVars() { 
		// G.v().out.println("resetUsedLocalVars");
		usedLocalVars = new HashSet<String> (); 
	}
	public void resetIntermediateVars() { intermediateVars = new HashSet<String> (); }
	public int getOffsetFromLine(String line) {
		int p1 = line.indexOf(':');
		int p2 = line.substring(0,p1).lastIndexOf(' ');
		return Integer.parseInt(line.substring(p2+1,p1));
	}
	public int getSetupInsn(int offset) {
		if(ifToSetup.containsKey(offset)) return ifToSetup.get(offset);
		else return -1;
	}
}

