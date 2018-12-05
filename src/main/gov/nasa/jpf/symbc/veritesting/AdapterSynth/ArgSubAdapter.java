package gov.nasa.jpf.symbc.veritesting.AdapterSynth;

public class ArgSubAdapter {
    public boolean[] i_is_const;
    public int[] i_val;

    public boolean b_is_const[];
    public int b_val[];

    public boolean c_is_const[];
    public int c_val[];

    public ArgSubAdapter(boolean[] i_is_const, int[] i_val, boolean[] b_is_const, int[] b_val, boolean[] c_is_const,
                         int[] c_val) {
        this.i_is_const = i_is_const;
        this.i_val = i_val;
        this.b_is_const = b_is_const;
        this.b_val = b_val;
        this.c_is_const = c_is_const;
        this.c_val = c_val;
    }

    @Override
    public String toString() {
        StringBuilder ret = new StringBuilder();
        for (int i = 0; i < 6; i++) ret.append(i_is_const[i]).append(",").append(i_val[i]).append(",");
        for (int i = 0; i < 6; i++) ret.append(b_is_const[i]).append(",").append(b_val[i]).append(",");
        for (int i = 0; i < 5; i++) ret.append(c_is_const[i]).append(",").append(c_val[i]).append(",");
        ret.append(c_is_const[5]).append(",").append(c_val[5]).append(",");
        return ret.toString();
    }
}
