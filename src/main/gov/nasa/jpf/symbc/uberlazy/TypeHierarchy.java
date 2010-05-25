package gov.nasa.jpf.symbc.uberlazy;

import java.util.ArrayList;
import java.util.HashMap;

import org.apache.bcel.classfile.JavaClass;

import gov.nasa.jpf.Config;
import gov.nasa.jpf.jvm.ClassInfo;
import gov.nasa.jpf.jvm.ThreadInfo;

/*
 * This class should build the type hierarchy of classes. 
 */

public class TypeHierarchy {

	protected static ReadFiles rf = null; 
	protected static ArrayList<ClassInfo> allClassInfos;
	public static HashMap<String, ArrayList<String>> typeHierarchies;
	
	public static void buildTypeHierarchy(ThreadInfo ti) {
	
		Config config = ti.getVM().getConfig();
		//get the path to the directories that contain
		//the files that we need account for the types
		//get the classes loaded if they are not previously
		String[] type_classpath = config.getStringArray("type_classpath");
		if(type_classpath != null) {
			rf = new ReadFiles(type_classpath);
			ArrayList<JavaClass> classFiles = rf.getClassFiles();
			TypeHierarchy.allClassInfos = new ArrayList<ClassInfo>();
			
			for(int classIndex = 0; classIndex < classFiles.size(); classIndex++) {
				JavaClass jc = classFiles.get(classIndex);
				// if this class wasn't loaded as part of the initialization
				// of the vm, we need to load the class in the vm. 
				// TODO: handle the case when it cannot be initialized
				ClassInfo ci = ClassInfo.getResolvedClassInfo(jc.getClassName());
				TypeHierarchy.allClassInfos.add(ci);
			}

			buildClassHierarchy();
		}
	}
	
	protected static void buildClassHierarchy() {
		
		typeHierarchies = new HashMap<String, ArrayList<String>>();
		
		for(int firstIndex = 0 ; firstIndex < TypeHierarchy.allClassInfos.size();
																	firstIndex++) {
			
			for(int secondIndex = (firstIndex+1); secondIndex 
					< TypeHierarchy.allClassInfos.size(); secondIndex++) {
				
				ClassInfo one = TypeHierarchy.allClassInfos.get(firstIndex);
				ClassInfo two = TypeHierarchy.allClassInfos.get(secondIndex);
				
				if(one.isInstanceOf(two) && !one.isAbstract()) {
					addElement(typeHierarchies,two.getName(),one.getName());
				} else if (two.isInstanceOf(one) && !two.isAbstract()) {
					addElement(typeHierarchies,one.getName(),two.getName());
				}
			}
		}
	}
	
	protected static void addElement (HashMap<String, ArrayList<String>> typeH, 
												String parent, String child) {
		ArrayList<String> children;
		if(typeH.containsKey(parent)) {
			 children = typeH.get(parent);	
		} else {
			children = new ArrayList<String>();
		}
		children.add(child);
		typeH.put(parent, children);
	}
	
	public static int getNumOfElements(String typeInfo) {
		if(TypeHierarchy.typeHierarchies == null) {
			System.err.println("Warning: the type_classpath configuration parameter" +
					" not set--the type hierarchies are empty");
			return 0;
		}
		if(TypeHierarchy.typeHierarchies.containsKey(typeInfo)) {
			return TypeHierarchy.typeHierarchies.get(typeInfo).size();
		}
		// there are no sub-classes in the type hierarchy
		return 0;
	}
	
	// get list of all sub-class names in the type heirarchy for the
	// class of "typeInfo". 
	public static ArrayList<String> getTypeElements(String typeInfo) {
		if(TypeHierarchy.typeHierarchies.containsKey(typeInfo)) {
			return TypeHierarchy.typeHierarchies.get(typeInfo);
		}
		// if there are no sub-classes then return an empty list
		return new ArrayList<String>();
	}
	
	public static ClassInfo getClassInfo(String typeInfo, int counter) {
		String index = TypeHierarchy.typeHierarchies.get(typeInfo).get(counter);
		for(int classIndex = 0; classIndex < TypeHierarchy.allClassInfos.size(); classIndex++) {
			ClassInfo ci = TypeHierarchy.allClassInfos.get(classIndex);
			if(ci.getName().equals(index)) {
				return ci;
			}
		}
		return null;
	}
	
}
