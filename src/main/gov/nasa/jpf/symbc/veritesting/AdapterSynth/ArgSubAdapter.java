package gov.nasa.jpf.symbc.veritesting.AdapterSynth;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;

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

    public static void writeAdapter(ObjectOutputStream out, ArgSubAdapter argSub) throws IOException {
        for (int i = 0; i < 6; i++) { out.writeBoolean(argSub.i_is_const[i]); out.writeInt(argSub.i_val[i]); }
        for (int i = 0; i < 6; i++) { out.writeBoolean(argSub.b_is_const[i]); out.writeInt(argSub.b_val[i]); }
        for (int i = 0; i < 6; i++) { out.writeBoolean(argSub.c_is_const[i]); out.writeInt(argSub.c_val[i]); }
    }

    public static ArgSubAdapter readAdapter(ObjectInputStream in) throws IOException {
        ArgSubAdapter argSub = new ArgSubAdapter(new boolean[6], new int[6], new boolean[6], new int[6], new boolean[6], new int[6]);
        for (int i = 0; i < 6; i++) { argSub.i_is_const[i] = in.readBoolean(); argSub.i_val[i] = in.readInt(); }
        for (int i = 0; i < 6; i++) { argSub.b_is_const[i] = in.readBoolean(); argSub.b_val[i] = in.readInt(); }
        for (int i = 0; i < 6; i++) { argSub.c_is_const[i] = in.readBoolean(); argSub.c_val[i] = in.readInt(); }
        return argSub;
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
