package gov.nasa.jpf.symbc.realtime;
/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class InstructionTimingInfo {

	private int opcode, bcet, wcet;
	private String mnemonic;
	
	public InstructionTimingInfo(String mnemonic, int opcode, int bcet, int wcet) {
		this.opcode = opcode;
		this.bcet = bcet;
		this.wcet = wcet;
		this.mnemonic = mnemonic;
	}

	public int getOpcode() {
		return opcode;
	}

	public int getBcet() {
		return bcet;
	}

	public int getWcet() {
		return wcet;
	}
	
	public void setWcet(int wcet) {
		this.wcet = wcet;
	}

	public void setBcet(int bcet) {
		this.bcet = bcet;
	}
	
	public String getMnemonic() {
		return mnemonic;
	}
	
}
