package sequences;



/**
 *
 * @author Mithun Acharya
 * Taken from Inkumsah, Xie's ASE08 paper
 */
public class BankAccount {
	private int balance;
	private int numberOfWithdrawals;


	public BankAccount(int amount){
		balance = amount;
	}


	public void deposit(int amount){
		if (amount>0)
			System.out.println("I am easily reachable in deposit");
			balance = balance + amount;
	}


	public void withdraw(int amount){
		if(amount>balance){
			System.out.println("I am easily reachable in withdraw");
			return;
		}
		if (numberOfWithdrawals>=5){// was 10
			System.out.println("I am very hard to reach in withdraw");
			return;
		}
		balance = balance - amount;
		numberOfWithdrawals++;
	}
}
