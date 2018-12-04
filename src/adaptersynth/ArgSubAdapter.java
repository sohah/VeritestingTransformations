import gov.nasa.jpf.symbc.Debug;

class ArgSubAdapter {
    boolean i_is_const[] = new boolean[6];
    int i_val[] = new int[6];

    boolean b_is_const[] = new boolean[6];
    int b_val[] = new int[6];

    boolean c_is_const[] = new boolean[6];
    int c_val[] = new int[6];

    ArgSubAdapter() {
        for (int i=0; i < 6; i++) {
            i_is_const[i] = Debug.makeSymbolicBoolean("i_is_const" + i);
            i_val[i] = Debug.makeSymbolicInteger("i_val" + i);
            b_is_const[i] = Debug.makeSymbolicBoolean("b_is_const" + i);
            b_val[i] = Debug.makeSymbolicInteger("b_val" + i);
            c_is_const[i] = Debug.makeSymbolicBoolean("c_is_const" + i);
            c_val[i] = Debug.makeSymbolicInteger("c_val" + i);
        }
    }
}
