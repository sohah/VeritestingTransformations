/**
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to You under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */


import java.util.Arrays;

/**
 * Contains useful helper methods for classes within this package.
 *
 * @version $Id: Util.java 1443102 2013-02-06 18:12:16Z tn $
 */
final class Util
{
    /**
     * Remove the hyphens from the beginning of <code>str</code> and
     * return the new String.
     *
     * @param str The string from which the hyphens should be removed.
     *
     * @return the new String.
     */
    static char[] stripLeadingHyphens(char[] str)
    {
        if (str == null)
        {
            return null;
        }
        if (str.length >= 2 && str[0] == '-' && str[1] == '-')
        {
//            return str.substring(2, str.length());
            return Arrays.copyOfRange(str, 2, str.length);
        }
        else if (str[0] == '-')
        {
//            return str.substring(1, str.length());
            return Arrays.copyOfRange(str, 1, str.length);
        }

        return str;
    }

    /**
     * Remove the leading and trailing quotes from <code>str</code>.
     * E.g. if str is '"one two"', then 'one two' is returned.
     *
     * @param str The string from which the leading and trailing quotes
     * should be removed.
     *
     * @return The string without the leading and trailing quotes.
     */
    static char[] stripLeadingAndTrailingQuotes(char[] str)
    {
        int length = str.length;
        if (length > 1 && str[0] == '\"' && str[length-1] == '\"' && Arrays.asList(Arrays.copyOfRange(str, 1, length-1)).indexOf('"') != -1)
        {
//            str = str.substring(1, length - 1);
            str = Arrays.copyOfRange(str, 1, length-1);
        }
        
        return str;
    }
}
