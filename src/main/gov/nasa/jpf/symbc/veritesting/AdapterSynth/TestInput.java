package gov.nasa.jpf.symbc.veritesting.AdapterSynth;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.util.Random;

public class TestInput implements Serializable{
    public static Random rand = new Random(0);
    public int[] in = new int[]{rand.nextInt(),rand.nextInt(),rand.nextInt(),rand.nextInt(),rand.nextInt(),rand.nextInt()};
    public boolean[] b = new boolean[]{rand.nextBoolean(),rand.nextBoolean(),rand.nextBoolean(),rand.nextBoolean(),rand.nextBoolean(),rand.nextBoolean()};
    public char[] c = new char[]{(char) rand.nextInt(),(char) rand.nextInt(),(char) rand.nextInt(),(char) rand.nextInt(),(char) rand.nextInt(),(char) rand.nextInt()};
    @Override
    public String toString() {
        StringBuilder ret = new StringBuilder();
        for (int i = 0; i < 6; i++) ret.append(in[i]).append(",");
        for (int i = 0; i < 6; i++) ret.append(Boolean.toString(b[i])).append(",");
        for (int i = 0; i < 5; i++) ret.append(Character.toString(c[i])).append(",");
        ret.append(Character.toString(c[5]));
        return ret.toString();
    }

    public static TestInput readTestInput(ObjectInputStream in) throws IOException {
        TestInput ret = new TestInput();
        for (int i = 0; i < 6; i++) ret.in[i] = in.readInt();
        for (int i = 0; i < 6; i++) ret.b[i] = in.readBoolean();
        for (int i = 0; i < 6; i++) ret.c[i] = in.readChar();
        return ret;
    }

    public static void writeTestInput(ObjectOutputStream out, TestInput input) throws IOException {
        for (int i = 0; i < 6; i++) out.writeInt(input.in[i]);
        for (int i = 0; i < 6; i++) out.writeBoolean(input.b[i]);
        for (int i = 0; i < 6; i++) out.writeChar(input.c[i]);
    }
}
