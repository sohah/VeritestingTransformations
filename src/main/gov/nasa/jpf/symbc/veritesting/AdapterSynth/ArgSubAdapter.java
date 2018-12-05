package gov.nasa.jpf.symbc.veritesting.AdapterSynth;

public class ArgSubAdapter {
    public boolean[] i_is_const;
    public int[] i_val;

    public boolean b_is_const[];
    public int b_val[];

    public boolean c_is_const[];
    public int c_val[];

    public ArgSubAdapter(boolean[] i_is_const, int[] i_val, boolean[] b_is_const, int[] b_val, boolean[] c_is_const, int[] c_val) {
        this.i_is_const = i_is_const;
        this.i_val = i_val;
        this.b_is_const = b_is_const;
        this.b_val = b_val;
        this.c_is_const = c_is_const;
        this.c_val = c_val;

    }
}
