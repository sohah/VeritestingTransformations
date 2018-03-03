public class testExceptions {
    public static void main(String[] args) {
        int x[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20};
        try {
            (new testExceptions()).excepA(x);
            (new testExceptions()).excepB(x);
            (new testExceptions()).excepC(x);
            (new testExceptions()).excepD(x);
            (new testExceptions()).excepE(x);
        }
        catch (Exception e){
            System.out.print("exception is raised");
        }
    }

    //an example where an exception that is thrown and caught within the same method
    public int excepA(int[] x) throws MyException {
        int total =0;
        try{
            for(int i=0; i<x.length; i++)
                total += x[i];
            if (total>100)
                throw new MyException("MyException raised");
        }
        catch (MyException e){
            System.out.println("Total is greater than 100 is caught");
        }
        return total;
    }

    //an example where an exception is thrown and not caught within the same method,
    public int excepB(int[] x) throws MyException {
        int total = 0;
        for (int i = 0; i < x.length; i++)
            total += x[i];
        if (total > 100)
            throw new MyException("MyException raised");
        return total;
    }

//an example with a try/catch block that does not locally throw an exception.
    public int excepC(int[] x) throws Exception {
        int total =0;
        try{
            total = excepA(x);
        }
        catch (MyException e){
            System.out.println("Total is greater than 100 is caught");
        }
        return total;
    }

    //an example with a try/finally block that does not locally throw an exception.
    public int excepD(int[] x) throws MyException {

        int total =0;
        try{
            for(int i=0; i<x.length; i++)
                total += x[i];
        }
        finally {
            System.out.println("Total is " + total);
        }
        return total;
    }
//an example with a try/catch/finally block that does not locally throw an exception.
    public int excepE(int[] x) throws MyException {
        int total =0;
        try{
            total = excepA(x);
        }
        catch (MyException e){
            System.out.println("Total is greater than 100 is caught");
        }
        finally {
            System.out.println("total is " + total);
        }
        return total;
    }
}


class MyException extends Exception{
    public MyException(String s){
        super(s);
    }
}


