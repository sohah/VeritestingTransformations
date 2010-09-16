package gov.nasa.jpf.symbc.strings;

public class MysteryQuestionMin {
	
	public static void main (String[] args) {
		preserveSomeHtmlTagsAndRemoveWhitespaces("b");
	}
	
	public static String preserveSomeHtmlTagsAndRemoveWhitespaces(String body) {
		if (body == null)
			return body;
		int i = 0;
		int len = body.length();
		int old = -1;
		while (i < len) {
			if (i <= old) {
				throw new RuntimeException ("Problem found");
			}
			old = i;
			char c = body.charAt(i);
			if (c == '<') {
				if (i + 14 < len &&
				(body.charAt(i + 8) == '\"')
				&&
				(body.charAt(i + 7) == '=')
				&&
				(body.charAt(i + 6) == 'f' || body.charAt(i + 6) == 'F')
				&&
				(body.charAt(i + 5) == 'e' || body.charAt(i + 5) == 'E')
				&&
				(body.charAt(i + 4) == 'r' || body.charAt(i + 4) == 'R')
				&&
				(body.charAt(i + 3) == 'h' || body.charAt(i + 3) == 'H')
				&&
				(body.charAt(i + 2) == ' ')
				&&
				(body.charAt(i + 1) == 'a' || body.charAt(i + 1) == 'A')
				) {
					int idx = i + 9;
					int idx2 = body.indexOf("\"", idx);
					int idxStart = body.indexOf('>', idx2);
					int idxEnd = body.indexOf("</a>", idxStart);
					if (idxEnd == -1)
						idxEnd = body.indexOf("</A>", idxStart);
					i = idxEnd + 4;
					continue;
				}
			}

		}
		return "";
	}
}
