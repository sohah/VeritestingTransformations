import java.io.Serializable;
import java.util.Random;

public class TestInput implements Serializable{
    Random rand = new Random();
    int in[] = new int[]{rand.nextInt(),rand.nextInt(),rand.nextInt(),rand.nextInt(),rand.nextInt(),rand.nextInt()};
    boolean b[] = new boolean[]{rand.nextBoolean(),rand.nextBoolean(),rand.nextBoolean(),rand.nextBoolean(),rand.nextBoolean(),rand.nextBoolean()};
    char c[] = new char[]{(char) rand.nextInt(),(char) rand.nextInt(),(char) rand.nextInt(),(char) rand.nextInt(),(char) rand.nextInt(),(char) rand.nextInt()};
    @Override
    public String toString() {
        StringBuilder ret = new StringBuilder();
        for (int i = 0; i < 6; i++) ret.append(in[i]).append(",");
        for (int i = 0; i < 6; i++) ret.append(Boolean.toString(b[i])).append(",");
        for (int i = 0; i < 5; i++) ret.append(Character.toString(c[i])).append(",");
        ret.append(Character.toString(c[5]));
        return ret.toString();
    }
}
