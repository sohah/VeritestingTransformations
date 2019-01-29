package gov.nasa.jpf.symbc.veritesting.RangerDiscovery;

import java.util.ArrayList;

public class Permutation {
    private static ArrayList<ArrayList> allPermutations = new ArrayList<>();

    /**
     * Print permutation of array elements.
     *
     * @param arr
     * @return count of permutation,
     */
    public static ArrayList<ArrayList> permutation(ArrayList arr) {
        allPermutations = new ArrayList<>();
        return permutation(arr, 0);
    }

    /**
     * Print permutation of part of array elements.
     *
     * @param arr
     * @param n
     *            start index in array,
     * @return count of permutation,
     */
    private static ArrayList<ArrayList> permutation(ArrayList arr, int n) {
        for (int i = n; i < arr.size(); i++) {
            swapArrEle(arr, i, n);
            permutation(arr, n + 1);
            swapArrEle(arr, n, i);
        }
        if (n == arr.size() - 1) {
            allPermutations.add(new ArrayList(arr));
            System.out.println(arr);
        }

        return allPermutations;
    }

    /**
     * swap 2 elements in array,
     *
     * @param arr
     * @param i
     * @param k
     */
    private static void swapArrEle(ArrayList arr, int i, int k) {
        Object tmp = arr.get(i);
        arr.set(i, arr.get(k));
        arr.set(k, tmp);
    }
}
