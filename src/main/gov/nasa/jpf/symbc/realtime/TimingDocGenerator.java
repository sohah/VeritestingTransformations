package gov.nasa.jpf.symbc.realtime;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import java.util.logging.Logger;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;
/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class TimingDocGenerator {
	
	public static TimingDoc generate(String timingDocPath) {
		TimingDoc doc = new TimingDoc();
		
		File fXmlFile = new File(timingDocPath);
		DocumentBuilderFactory dbFactory = DocumentBuilderFactory.newInstance();
		DocumentBuilder dBuilder;
		try {
			dBuilder = dbFactory.newDocumentBuilder();
		} catch (ParserConfigurationException e) {
			throw new TimingDocException(e);
		}
		Document timingmodelDoc;
		try {
			timingmodelDoc = dBuilder.parse(fXmlFile);
		} catch (SAXException e) {
			throw new TimingDocException(e);
		} catch (IOException e) {
			throw new TimingDocException(e);
		}
		
		NodeList nList = timingmodelDoc.getElementsByTagName("JavaByteCode");
		for(int i = 0; i < nList.getLength(); i++) {
			Node nNode = nList.item(i);	 
			if (nNode.getNodeType() == Node.ELEMENT_NODE) {
				Element jbcEle = (Element) nNode;
				int opcode = Integer.parseInt(jbcEle.getElementsByTagName("opcode").item(0).getTextContent());
				String mnemonic = jbcEle.getElementsByTagName("mnemonic").item(0).getTextContent();
				int bcet = Integer.parseInt(jbcEle.getElementsByTagName("BCET").item(0).getTextContent());
				int wcet = Integer.parseInt(jbcEle.getElementsByTagName("WCET").item(0).getTextContent());
				
				doc.put(mnemonic, new InstructionTimingInfo(mnemonic, opcode, bcet, wcet));
			}
		}
		return doc;
	}
}
