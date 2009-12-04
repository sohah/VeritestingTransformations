package gov.nasa.jpf.symbc.uberlazy;
/**
//@author Neha Rungta
//the class builds a list of full qualified paths to the files
//that are to be considered while constructing the type hierarchy
//between classes in the presence for programs with polymorphism 
// this is required because the classes that we want to be considered
// in the symbolic execution framework maybe not loaded in the
// vm. Only classes with explicit references are loaded in the core vm.
 */

import java.io.File;
import java.io.FilenameFilter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;

import org.apache.bcel.classfile.ClassFormatException;
import org.apache.bcel.classfile.ClassParser;
import org.apache.bcel.classfile.JavaClass;

public class ReadFiles {
	
	private String fileSeparator;
	public ArrayList<JavaClass> classFiles;
	
	
	public ArrayList<JavaClass> getClassFiles() {
		return classFiles; 
	}
	
	public ReadFiles(String[] directoryPaths) {
		classFiles = new ArrayList<JavaClass>();
		//Using file separator ensures it works on all architectures
		fileSeparator = System.getProperty("file.separator");
		for(int dirIndex = 0; dirIndex < directoryPaths.length; dirIndex++) {
			getAllFileNames(directoryPaths[dirIndex]);
		}
	}
	
	FilenameFilter filter = new FilenameFilter() {
		public boolean accept(File dir, String name) {
			if(!name.startsWith(".")) {
				if(name.contains(".class")) {
					return true;
				}
			}
			return false;
		}
	};
	
	FilenameFilter filterDirName = new FilenameFilter() {
		public boolean accept(File dir, String name) {
			String dirName = dir.getAbsolutePath().concat(fileSeparator+name);
			File newDirName = new File(dirName);
			boolean isdir = newDirName.isDirectory();
			// this will not list the directories that are hidden or 
			// are part of the version control like ".svn" or ".hg"
			if(!name.startsWith(".")){
					return isdir;
			}
			return false;
		}
	};
	

	
	private void getAllFileNames(String directoryPath) {
		File dir = new File(directoryPath);
		String[] subDir = dir.list(filterDirName);
		String[] files = dir.list(filter);
				
		for(int i = 0; i < files.length; i++) {
			constructJavaClasses(directoryPath.concat(fileSeparator + files[i]));
		}
		
		for(int subDirIndex = 0; subDirIndex < subDir.length; subDirIndex++) {
			getAllFileNames(directoryPath.concat(fileSeparator + subDir[subDirIndex]));
		}
	}
	
	private void constructJavaClasses(String path) {
		File f = new File(path);
		if (f.exists()) {	
			try {
				classFiles.addAll(parseClass(f));
			} catch (IOException e) {
				System.err.println("There was an error while parsing" +
						" the class file: " + path );
			}
		}
		else{
			System.err.println("Could not find file: " + f.getName());
			System.exit(1);
		}
	}
	

	private Collection<JavaClass> parseClass(File f) throws IOException {
		Collection<JavaClass> result = new ArrayList<JavaClass>();
		ClassParser cp = new ClassParser(f.getAbsolutePath());
		try {
			result.add((JavaClass) cp.parse());

		} catch (ClassFormatException e) {
			System.err.println("There was an error while parsing");
		}
		return result;
	}
	
}