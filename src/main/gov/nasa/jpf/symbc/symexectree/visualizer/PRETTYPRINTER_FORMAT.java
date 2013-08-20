/**
 * 
 */
package gov.nasa.jpf.symbc.symexectree.visualizer;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */

// Feel free to add more
public enum PRETTYPRINTER_FORMAT {
	DOT("dot"),
	PNG("png"),
	EPS("eps"),
	PDF("pdf");
	
	private String format;

	PRETTYPRINTER_FORMAT(String format) {
		this.format = format;
	}
	
	public String getFormat() {
		return this.format;
	}
}
