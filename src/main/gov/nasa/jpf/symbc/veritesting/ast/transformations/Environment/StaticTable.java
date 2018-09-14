package gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment;

import java.util.Set;

/**
 * Base class for all environment tables.
 */


public class StaticTable<V> extends Table<Integer, V>{

    public StaticTable(String region_input_table, String var, String s) {
        super(region_input_table, var, s);
    }



    /**
     * Updates a key of the table for a specific entry.
     */

    public void updateKey(Integer oldKey, Integer newKey) {
        Object[] keys = table.keySet().toArray();
        for (int i = 0; i < keys.length; i++) {
            V value = table.get(keys[i]);
            if (keys[i] == oldKey) {
                table.put(newKey, value);
                table.remove(oldKey);
            }
        }
    }


    //TODO: Soha remove this.
/*

    */
/**
     * Appends a postfix to each key in the table.
     *
     * @param unique A unquie postfix.
     *//*


    public void makeUniqueKey(int unique) {
        List keys = new ArrayList(table.keySet());
        Collections.sort(keys);
        Collections.reverse(keys);
        Iterator itr = keys.iterator();
        while (itr.hasNext()) {
            Integer key = (Integer) itr.next();
            String varId = Integer.toString(key);
            varId = varId.concat(Integer.toString(unique));
            table.put(Integer.valueOf(varId), table.get(key));
            table.remove(key);
        }
    }

*/

    /**
     * Merge the table with the eateries of another table.
     */

    public void mergeTable(StaticTable<V> t) {
        this.table.putAll(t.table);
    }


    public Set<Integer> getKeys() {
        return table.keySet();

    }
}
