public class RacerS implements Runnable {
    int d = 42;

    public void run () {
//        doSomething(1001);
d=1;
    //    setD(true);                            // (1)

    }

    private void setD(boolean flag) {
        if(flag)
            d = 0;
    }

    public static void main (String[] args){
        System.out.println("inside my racerS!");
        RacerS racerS = new RacerS();
        Thread t = new Thread(racerS);
        t.start();

        doSomething(1000);
        int c = 420 / racerS.d;              // (2)
        System.out.println(c);
    }

    static void doSomething (int n) {
        try { Thread.sleep(n); } catch (InterruptedException ix) {}
    }
}