import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

public class ISSTAExample {

    public static void main(String[] args) {
        System.out.println("Hello World!");

        String string = "test the example in the paper ";
        List<Character> textList = string.chars().mapToObj((i) -> Character.valueOf((char)i)).collect(Collectors.toList());

        //(new Main()).paperExample(textList);

        ArrayList<Integer> numberList = new ArrayList<Integer>(Arrays.asList(0,1,1,1,0, 1,1, 0,0, 1,1,1,1,1,1,0));

        (new ISSTAExample()).paperExampleNum(numberList);


    }


    public int paperExampleNum(List<Integer> numList) {
        int wordCount = 0;
        boolean inWord;

        if (numList.size() > 0) { //would be nice if we have early return here.
            if(numList.get(0) == 0)
                inWord = false;
            else
                inWord = true;

            for (int i = 0; i < numList.size(); i++) {
                if (inWord) {
                    if (numList.get(i) == 0) { //0 means there is a whitespace
                        ++wordCount;
                        inWord = false;
                    }
                } else {
                    if (numList.get(i) != 0) { // non whitespace.
                        inWord = true;
                    }
                }
            }
        }
        System.out.println("Number of words is:" + wordCount);
        return wordCount;
    }


    public int paperExample(List<Character> textList){
        boolean inWord = false;
        int wordCount = 0;

        for(int i = 0; i < textList.size(); i++){
            if(inWord){
                if(Character.isWhitespace(textList.get(i))){
                    ++wordCount;
                    inWord = false;
                }
            }
            else{
                if(!Character.isWhitespace(textList.get(i))){
                    inWord = true;
                }
            }
        }

        System.out.println("Number of words is:" + wordCount);

        return wordCount;
    }

    public int paperExampleNum(int x1, int x2, int x3, int x4, int x5, int x6) {

        ArrayList<Integer> numberList = new ArrayList<Integer>(Arrays.asList(x1, x2, x3, x4, x5, x6));

        int wordCount = 0;
        boolean inWord;

        if (numberList.size() > 0) { //would be nice if we have early return here.
            int firstEement = numberList.get(0);
            if (x1 == 0)
                inWord = false;
            else
                inWord = true;

            for (int i = 0; i < numberList.size(); i++) {
                if (inWord) {
                    if (numberList.get(i) == 0) { //0 means there is a whitespace
                        ++wordCount;
                        inWord = false;
                    }
                } else {
                    if (numberList.get(i) != 0) { // non whitespace.
                        inWord = true;
                    }
                }
            }
        }
        System.out.println("Number of words is:" + wordCount);
        return wordCount;
    }
}
