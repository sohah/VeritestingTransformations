public class VeritestingPerf {

    public int count = 0;

    public static void main(String[] args) {

        /**************** create New Object Tests ************/
        //(new VeritestingPerf()).createObjectTC1(true, true);
        //(new VeritestingPerf()).createObjectTC2(true, true);
        //(new VeritestingPerf()).createObjectTC3(true, true);
        //(new VeritestingPerf()).createObjectTC4(true, true);
        //(new VeritestingPerf()).createObjectTC5(true, true);
        //(new VeritestingPerf()).createObjectTC6(true, true);
        //(new VeritestingPerf()).createObjectTC7(true, true);
        //(new VeritestingPerf()).createObjectTC8(true, true);
        //(new VeritestingPerf()).createObjectTC9(true, true);
        //(new VeritestingPerf()).createObjectTC10(true, true);
        //(new VeritestingPerf()).assertRegions(true, true);
        //(new VeritestingPerf()).createObjectComplexRegionTC1(true, true);
        //(new VeritestingPerf()).createObjectComplexRegionTC2(true, true);
        //(new VeritestingPerf()).createObjectComplexRegionTC3(true, true);
        //(new VeritestingPerf()).createObjectComplexRegionTC4(true, true);
        //(new VeritestingPerf()).createObjectComplexRegionTC5(true, true);
        //(new VeritestingPerf()).createObjectComplexRegionTC6(true, true);
        //(new VeritestingPerf()).createObjectComplexRegionTC7(true, true);
        //(new VeritestingPerf()).createObjectComplexRegionTC8(true, true);

        /****************** arrayLoad Tests ********************/
        //(new VeritestingPerf()).testSegment1(true, true, 2);
        //(new VeritestingPerf()).testSegment2(true, true, 2);
        //(new VeritestingPerf()).inRangeloadArrayTC(22, 2);
//        (new VeritestingPerf()).innerCatchOutRangeloadArrayTC(22, 2);
//        (new VeritestingPerf()).outRangeloadArrayTC( 22, 2);
        // (new VeritestingPerf()).catchOutRangeloadArrayTC(22, 2);
        //(new VeritestingPerf()).boundedOutRangeloadArrayTC(22, 2);
        //(new VeritestingPerf()).segmantTest(22, 2);
        //(new VeritestingPerf()).assertRegions(true,true);

        /****************** arrayStore Tests ********************/
        //int a[] = {200, 300};
        //(new VeritestingPerf()).arrayStoreTC1(1, 2);
        //(new VeritestingPerf()).arrayStoreTC2(1, 2, a);
        //(new VeritestingPerf()).arrayStoreTC3(1, 2, a);
        //(new VeritestingPerf()).arrayStoreTC4(1, 2, a);
        //(new VeritestingPerf()).arrayStoreTC5(1, 2, a);
        //(new VeritestingPerf()).arrayStoreTC6(1, 2);
        //(new VeritestingPerf()).arrayStoreTC7(1, 2);
        //(new VeritestingPerf()).arrayLoadTC1(1,2);

        //(new VeritestingPerf()).arrayLoad0(1,2);

        /****************** getFieldSPFCases Tests ********************/
        //(new VeritestingPerf()).getFieldSPFCaseTC1(true);
        //(new VeritestingPerf()).fieldTest1(1);
        //(new VeritestingPerf()).fieldTest00(1);

        /****************** ir Tests ********************/
        //(new VeritestingPerf()).irTest1(1);
        //(new VeritestingPerf()).irTest2(1);
        //(new VeritestingPerf()).irTest3(1);
        //(new VeritestingPerf()).irTest4(1);
        //(new VeritestingPerf()).irTest5(1);
//        (new VeritestingPerf()).irTest6(1);
        (new VeritestingPerf()).foo7(1);



        //(new VeritestingPerf()).nestedRegionThrowsException(0);
//        (new VeritestingPerf()).simpleRegionThrowsException(0);


//        (new VeritestingPerf()).cfgTest(1);
//        (new VeritestingPerf()).countBitsSet(1);
//        (new VeritestingPerf()).nestedRegion(1);
//        (new VeritestingPerf()).nestedRegion1(true, true);
//        (new VeritestingPerf()).testNestedMiddle(1);
//        (new VeritestingPerf()).testNested(1);
//        (new VeritestingPerf()).testDynObject(false, 1);
//        int x[] = {1, 2};
//        (new VeritestingPerf()).ifNull("Test");
//        (new VeritestingPerf()).foo(true);
//
//        System.out.println("!!!!!!!!!!!!!!! Start Testing! ");
//        (new VeritestingPerf()).testMe2(0,true);
//        (new VeritestingPerf()).readAfterWriteTest(1);
//        (new VeritestingPerf()).testSimple(1);
//
//        (new VeritestingPerf()).testSimple1(1);
//        (new VeritestingPerf()).simpleRegion(1);
//        (new VeritestingPerf()).fieldWriteTestBranch2(1);
//        (new VeritestingPerf()).fieldWriteTestBranch1(1);
//        (new VeritestingPerf()).testSimple2(1);
//        (new VeritestingPerf()).testSimpleFail(1);
//
//        int x[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20};
//        (new VeritestingPerf()).testMe5(x, 1);
//        (new VeritestingPerf()).testMe6(x, 12, -1, 1);
//        (new VeritestingPerf()).testMe4(x, 12, -1, 1);
//        (new VeritestingPerf()).arrayTest(x, 6);
//        (new VeritestingPerf()).checkOperator();
//        ArrayList<Integer> list = new ArrayList<>();
//        list.add(Debug.makeSymbolicInteger("a1"));
//        list.add(Debug.makeSymbolicInteger("a2"));
//        (new VeritestingPerf()).countArrayList(list);
    }

    /*
        private int nestedRegionThrowsException(int i) {
            if ( i != 0) {
                if (i < 0)
                throw new NullPointerException("negative");
                else i = 1;
            } else i = 2;
            return i;
        }

        public int simpleRegionThrowsException(int i) {
            int ret = -1;
            TempClass tempClass = new TempClass();
            if (i < 0) {
                throw new NullPointerException("negative");
    //            new NullPointerException("negative");
    //            assert true;
            }
            else ret = ret + tempClass.getTempInt();
            ret += 1;
            return ret;
        }

        public int simpleRegionEarlyReturn(int i) {
            int ret = -1;
            TempClass tempClass = new TempClass();
            if (i < 0)
                return -1;
            else ret = ret + tempClass.getTempInt();
            ret += 1;
            return ret;
        }

        public static void testMe2(int x, boolean b) {
            System.out.println("!!!!!!!!!!!!!!! First step! ");
            //System.out.println("x = " + x);
            int[] y = {1, 2};
            if (b) {
                x++;
                System.out.println("Program then branch");
            } else {
                x--;
                System.out.println("Program else branch");
            }
            x++;
        }

        private void testNested(int x) {
            testNestedMiddle(x);
            assert (x != 0 && x > 0 ? count == 3 : true);
            assert (x != 0 && x <= 0 ? count == 4 : true);
            assert (x == 0 ? count == 5 : true);
        }

        private int testNestedMiddle(int x) {
            int retval = 0;
            retval += nestedRegion(x);
    //        assert(x != 0 && x > 0 ? count == 3 : true);
    //        assert(x != 0 && x <= 0 ? count == 4 : true);
    //        assert(x ==0 ? count == 5 : true);
            return retval;
        }

        public int nestedRegion(int x) {
            //int count = 0;
            int a=8;
            if (x != 0) {
                if (x > 0) {
                    count = a/8;
                } else {
                    count = a/4;
                }
            } else {
                count = a/2;
            }
            assert(x != 0 && x > 0 ? count == (a/8) : true);
            assert(x != 0 && x <= 0 ? count == (a/4) : true);
            assert(x ==0 ? count == (a/2) : true);
            return count;
        }

        // from ProbExample1
        public int test(int x, int y, int z) {
            if (x > z) {
                //calcProb();
            }
            if (z > 0) {
                //calcProb();
            }
            System.out.println("now");
            if (y > 0) {
                System.out.println("now1");

                //calcProb();
            }
            return 0;

        }

        public int nestedRegion1(boolean x, boolean y) {
            //int a = 0;
            if (y) {
    //            a = 1;
                if (x) {
                    a = 2;
                } else {
                    a = 3;
                }
    //            a = 4;
            } else {
    //            a = 5;
                if (x) a = 6;
                else a = 7;
    //            a = 8;
            }
    //        assert (y ? a == 4 : true);
            assert (y && x ? a == 2 : true);
            assert (y && !x ? a == 3 : true);
    //        assert (!y ? a == 8 : true);
            assert (!y && x ? a == 6 : true);
            assert (!y && !x ? a == 7 : true);
            return a;
        }


        public int simpleRegion(int x) {
            //count = 4;
            if (x > 0) {
                count = 1;
                count = 3;
            } else {
                count = 2;
                count = 4;
            }
            return count;
        }

        public void testSimple(int x) {
            count = simpleRegion(x);
            assert (x > 0 ? count == 3 : true);
            assert (x <= 0 ? count == 4 : true);
            System.out.println("x: " + x + "; count: " + count);
        }

        public void testSimple1(int x) {
            //int count;
            System.out.println("Executing success case!");
            if (x != 0) {
                count = 3;
            } else {
                count = 4;
            }

            assert (x != 0 ? count == 3 : true);
            assert (x == 0 ? count == 4 : true);
        }

        public void testSimpleFail(int x) {
            System.out.println("Executing fail case!");
            int count;
            if (x > 0) {
                count = 3;
            } else {
                count = 4;
            }
            assert (x != 0 ? count == 3 : true);
            assert (x == 0 ? count == 4 : true);
        }

        public void testSimple2(int x) {
            //int count;
            if (x != 0) {
                if (x > 0) {
                    count = 3;
                } else {
                    count = 4;
                }
            } else {
                count = 5;
            }

            assert (x > 0 ? count == 3 : true);
            assert (x < 0 ? count == 4 : true);
            assert (x == 0 ? count == 5 : true);
        }


        public int countBitsSetSimple(int x) {
            //int count = 0;
            while (x != 0) {
                int lowbit = x & 1;
                int flag;// = 0;
                if (lowbit != 0) flag = 1;
                else flag = 0;
                count += flag;
                x = x >>> 1; // logical right shift
            }
            return count;
        }

        public int countBitsSet(int x) {
            TempClass tempClass = new TempClassDerived();
            int count = 0;
            int a = 1;
            int xOrig = x;
            //TempClass tempClass = new TempClass();
            while (x != 0) {
                if ((x & 1) != 0) {
                    // nested field access test case 1
                    //count += tempClass.tempClass2.tempInt2;
                    // nested field access test case 2
                    //TempClass2 tempClass2 = tempClass.tempClass2;
                    //tempClass2.tempInt2 += count;
                    // Test case 3: method summary test + higher order region test

                    count += tempClass.getOne(0);
                    //TempClassDerived.myInt = 1; //creates r/w interference with tempClass.getOne's method summary
                    // Test case 4: use this to test dynamic field access
                    //count += tempClass.myInt;
                    // Test case 5: testing read-after-write in a simple region
                    //count += 1;
    //                a += count;
    //                count += 2;
                    // Test case 6
                    //count += tempClass.nestedRegion(a);
                }
                x = x >>> 1; // logical right shift
            }
            assert (xOrig == 0 || TempClassDerived.tempInt == 6);
            if (x >= -15 && x < 16) assert (Bits.populationCount(xOrig) == count);
            System.out.println("TempClassDerived.tempInt = " + TempClassDerived.tempInt);
            System.out.println("TempClass.tempInt = " + TempClass.tempInt);
            return count;
        }

        public int readAfterWriteTest(int x) {
            TempClass tempClass1 = new TempClassDerived();
            TempClass tempClass2 = new TempClassDerived();
            count = 0;
            int a = 1;
            int xOrig = x;
            //TempClass tempClass = new TempClass();
            while (x != 0) {
                if ((x & 1) != 0) {
                    //tempClass1.tempInt += 1;
                    //a = tempClass2.tempInt; // should not cause a read after write
                    //tempClass1.tempInt += 1;
                    count += 1;
                }
                x = x >>> 1; // logical right shift
            }
            assert (xOrig == 0 ? count == 0 : true);
            assert (isPowerOf2(xOrig) ? count == 1 : true);
            System.out.println("a = " + a);
            return count;
        }

        public int fieldWriteTestBranch2(int x) {
            if (x != 0) count = 1;
            else count = 2;
            return count;
        }

        public int fieldWriteTestBranch1(int x) {
            if (x != 0) count = 1;
            return count;
        }

        //testing inRangeArrayLoad for symbolic & concrete field
        public int inRangeloadArrayTC(int field, int length) {
            int[] x = {300, 400};
            int temp = 1;
            try {
                if (length <= 0) {
                    //     System.out.println("executing then branch");
                    temp = 2;
                } else {
                    // System.out.println("executing else branch");
                    temp = x[field] + 2;
                }
            } catch (ArrayIndexOutOfBoundsException e) {
                temp = 3;
            }
            assert length <= 0 ? temp == 2 : true;
            assert length > 0 && field == 0 ? temp == 302 : true;
            assert length > 0 && field == 1 ? temp == 402 : true;
            assert length > 0 && field != 0 && field != 1 ? temp == 3 : true;
    //        Debug.printPC("vaibhav: pc = ");
    //        System.out.println("temp = " + temp);
            return temp;
        }

        //testing outRangeArrayLoad for symbolic field
        public int outRangeloadArrayTC(int field, int length) throws ArrayIndexOutOfBoundsException {
            int[] x = {300};
            int temp = 1;
            try {
                if (length > 0) {
                    temp = x[field];
                } else {
                    temp = 2;
                }
            } catch (ArrayIndexOutOfBoundsException e) {
                System.out.println("catch array out of bound, length = " + length + ", field = " + field);
                temp = 3;
            }
            System.out.println("temp = " + temp);

            assert ((length <= 0) ? (temp == 2) : true);
            assert (length > 0) && (field == 0)? (temp == 300 ) : true;
            assert (length > 0) && (field != 0)? (temp == 3 ) : true;
    //        if (temp == 1)
    //            System.out.println("then branch");
    //        else
    //            System.out.println("else branch");
            return 0;
        }

        public int catchOutRangeloadArrayTC(int field, int length) throws ArrayIndexOutOfBoundsException {
            int[] x = {1, 2};
            int temp = 1;
            int y = 1;
            try {
                if (length > 0) {
                    temp = x[field];
                } else {
                    temp = 1;
                }
            } catch (ArrayIndexOutOfBoundsException e) {
                System.out.println("catch array out of bound");
            }
            return temp;
        }


        public int innerCatchOutRangeloadArrayTC(int field, int length) throws ArrayIndexOutOfBoundsException {
            int[] x = {300};
            int temp = 1;
            int y = 1;
            if (length > 0) {
                try {
                    temp = x[field];
                } catch (ArrayIndexOutOfBoundsException e) {
                    System.out.println("catch array is out of bound");
                }
            } else {
                temp = 2;
            }
            return temp;
        }

        public int boundedOutRangeloadArrayTC(int field, int length) throws ArrayIndexOutOfBoundsException {
            int[] x = {300};
            int temp = 0;
            int y = 2;
            if (length > 0) {
                try {
                    temp = x[field];
                } catch (ArrayIndexOutOfBoundsException e) {
                    System.out.println("catch array out of bound");
                }
            } else {
                temp = 2;
            }

            if (temp != 0)
                y = 1;
            else
                y = 0;
            return y;
        }
    */
    /*public int createObjectTC1(boolean x, boolean y) {
        int a = 3;
        if (x) {
            TempClass tempClass2 = new TempClass();
            a = 4;
        }
//        assert(x ? a==0: true);
//        assert(!x ? a==3: true);
        return a;
    }*/
/*
    public int createObjectTC2(boolean x, boolean y) {
        int a = 0;
        if (x) {
            TempClass tempClass2 = new TempClass();
        } else {
            a = 3;
        }
//        assert(x ? a==0: true);
//        assert(!x ? a==3: true);
        return a;
    }

    public int createObjectTC3(boolean x, boolean y) {
        int a = 0;
        if (x) {
            a = 3;
        } else {
            a = 2;
            TempClass tempClass2 = new TempClass();
        }
//        assert(x ? a==2: true);
//        assert(!x ? a==3: true);
        return a;
    }

    public int createObjectTC4(boolean x, boolean y) {
        int a = 0;
        if (new TempClass3(x).valid) {
            a = 3;
        } else {
            a = 2;
        }
//        assert(a==3);
        return a;
    }


    public int createObjectTC5(boolean x, boolean y) {
        int a = 0;
        if (x) {
            TempClass tempClass2 = new TempClass();
        } else {
            a = 2;
            TempClass tempClass2 = new TempClass();
        }
//        assert(x ? a==2: true);
//        assert(!x ? a==3: true);
        return a;
    }

    public int createObjectTC6(boolean x, boolean y) {
        int a = 0;
        if (x) {
            a = 3 + a;
        } else {
            a = 2;
            TempClass tempClass2 = new TempClass();
        }
//        assert(x ? a==2: true);
//        assert(!x ? a==3: true);
        return a;
    }

    public int createObjectTC7(boolean x, boolean y) {
        int a = 3;
        if (x) {
   //         TempClass tempClass2 = new TempClass();
            a = 4;
        }
        if (y) {
            a = 4 + a;
        } else {
            a = 2 + a;
        }
        assert(x && y ? a == 8: true);
        assert(!x ? a==3: true);
        assert(x && !y ? a == 6: true);
        assert(!x && y ? a == 7: true);
        assert(!x && !y ? a == 5: true);
        return a;
    }


    public int createObjectTC8(boolean x, boolean y) {
        int a = 0;
        if (x) {
            a = 3 + a;
        } else {
            a = 2;
            TempClass tempClass2 = new TempClass();
        }

        if (y) {
            a = 4 + a;
            TempClass tempClass2 = new TempClass();
            a = 6 + a;
        } else {
            a = 2 + a;
        }
//        assert(x ? a==2: true);
//        assert(!x ? a==3: true);
        return a;
    }


    public int createObjectTC9(boolean x, boolean y) {
        int a = 3;
        TempClass tempClass2 = new TempClass();
        if (x) {
            a = 4;
        }
//        assert(x ? a==0: true);
//        assert(!x ? a==3: true);
        return a;
    }


    public int createObjectTC10(boolean x, boolean y) {
        int a = 3;
        if (x) {
            a = 4;
        }
        TempClass tempClass2 = new TempClass();
        ++a;
//        assert(x ? a==0: true);
//        assert(!x ? a==3: true);
        return a;
    }

    public int createObjectComplexRegionTC1(boolean x, boolean y) {
        int a = 0;
        if (y) {
            if (x) {
                a = 3;
            } else {
                a = 2;
                TempClass tempClass2 = new TempClass();
            }
        }

//        assert((y && x) ? a==3: true);
//        assert((y && !x) ? a==2: true);
//        assert(!y ? a==0: true);

        return a;
    }

    public int createObjectComplexRegionTC2(boolean x, boolean y) {
        int a = 0;
        if (y) {
            if (x) {
                a = 3;
                TempClass tempClass2 = new TempClass();
            } else {
                a = 2;
            }
        } else {
            if (x) {
                a = 3;
            } else {
                TempClass tempClass2 = new TempClass();
                a = 2;
            }
        }
//        assert((y && x) ? a==3: true);
//        assert((y && !x) ? a==2: true);
//        assert(!y ? a==0: true);

        return a;
    }

    public int createObjectComplexRegionTC3(boolean x, boolean y) {
        int a = 0;
        if (y) {
            if (new TempClass3(x).valid) {
                a = 3;
            } else {
                a = 2;
            }
        }
        return a;
    }

    //SH:Passed April 23rd.
    public int createObjectComplexRegionTC4(boolean x, boolean y) {
        int a = 0;
        if (y) {
            if (new TempClass3(false).valid) {
                a = 3;
            } else {
                a = 2;
            }
        }
//        assert(y ? a==2: true);
//        assert(!y ? a==0: true);

        return a;
    }

    public int createObjectComplexRegionTC5(boolean x, boolean y) {
        int a = 0;
        if (y) {
            TempClass tempClass1 = new TempClass();
            a = 1;
            if (x) {
                a = 3;
            } else {
                a = 2;
            }
        }
//        assert((y && x) ? a==3: true);
//        assert((y && !x) ? a==2: true);
//        assert(!y ? a==0: true);

        return a;
    }


    public int createObjectComplexRegionTC6(boolean x, boolean y) {
        int a = 0;
        if (new TempClass3(x).valid) {
            a = 1;
            if (x) {
                a = 3;
            } else {
                a = 2;
            }
        }
        return a;
    }

    public int createObjectComplexRegionTC7(boolean x, boolean y) {
        int a = 0;
        if (new TempClass3(true).valid) {
            a = 1;
            if (x) {
                a = 3;
            } else {
                a = 2;
            }
        }
        return a;
    }

    public int createObjectComplexRegionTC8(boolean x, boolean y) {
        int a = 0;
        if (y) {
            if (x) {
                a = 3;
                TempClass tempClass2 = new TempClass();
            } else {
                a = 2;
                TempClass tempClass2 = new TempClass();
            }
        } else {
            if (x) {
                a = 3;
                TempClass tempClass2 = new TempClass();
            } else {
                TempClass tempClass2 = new TempClass();
                a = 2;
            }
        }
//        assert((y && x) ? a==3: true);
//        assert((y && !x) ? a==2: true);
//        assert(!y ? a==0: true);

        return a;
    }*/

/*
    public int arrayLoadTC1(int field, int length) {
        int[] x = {300, 400};
        int temp = 1;
        try {
            if (length <= 0) {
                //     System.out.println("executing then branch");
                temp = 2;
            } else {
                // System.out.println("executing else branch");
                temp = x[temp] + 2;
            }
        } catch (ArrayIndexOutOfBoundsException e) {
            temp = 3;
        }
        assert length <= 0 ? temp == 2 : true;
        assert length > 0 && field == 0 ? temp == 302 : true;
        assert length > 0 && field == 1 ? temp == 402 : true;
        assert length > 0 && field != 0 && field != 1 ? temp == 3 : true;
//        Debug.printPC("vaibhav: pc = ");
//        System.out.println("temp = " + temp);
        return temp;
    }


    public int arrayStoreTC1(int field, int length) { // should be treated as a new object creation
        int[] x = {300, 400};
        int temp = 1;
        try {
            if (length <= 0) {
                //     System.out.println("executing then branch");
                temp = 2;
            } else {
                // System.out.println("executing else branch");
             //   x[field] = temp;
            }
        } catch (ArrayIndexOutOfBoundsException e) {
            temp = 3;
        }
        *//*Debug.printPC("Soha: pc = ");
        assert (length <= 0 ? x[0] == 300 & x[1] == 400 : true);
        assert (length > 0 && field == 0 ? x[0] == 1 && x[1] == 400 : true);
        assert (length > 0 && field == 1 ? x[0] == 300 && x[1] == 1 : true);
        *//*
        return temp;
    }


    public int arrayStoreTC2(int field, int length, int[] x) { //symbolic field - concrete operand
        int temp = 1;

        try {
            if (length <= 0) {
                temp = 2;
            } else {
                x[field] = temp;
            }
        }
        catch (ArrayIndexOutOfBoundsException e){
            temp = 3;
        }
        return temp;
    }


    public int arrayStoreTC3(int field, int length, int[] x) { //symbolic field - symbolic operand
        int temp = length;
        try {
            if (length <= 0) {
                //     System.out.println("executing then branch");
                temp = 2;
            } else {
                // System.out.println("executing else branch");
                x[field] = temp;
            }
        } catch (ArrayIndexOutOfBoundsException e) {
            temp = 3;
        }

        return temp;
    }

    public int arrayStoreTC4(int field, int length, int[] x) { //concrete field - concrete operand
        int temp = 1;
        try {
            if (length <= 0) {
                //     System.out.println("executing then branch");
                temp = 2;
            } else {
                // System.out.println("executing else branch");
                x[temp] = temp;
            }
        } catch (ArrayIndexOutOfBoundsException e) {
            temp = 3;
        }

        return temp;
    }


    public int arrayStoreTC5(int field, int length, int[] x) { //concrete field - concrete operand
        int temp = 1;
        try {
            if (length <= 0) {
                //     System.out.println("executing then branch");
                temp = 2;
            } else {
                // System.out.println("executing else branch");
                x[temp] = length;
            }
        } catch (ArrayIndexOutOfBoundsException e) {
            temp = 3;
        }

        return temp;
    }

    public int arrayStoreTC6(int field, int length) { // should be treated as a new object creation
        int[] x = {300, 400};
        int temp = 1;
        if (length <= 0) {
            //     System.out.println("executing then branch");
            temp = 2;
        } else {
            // System.out.println("executing else branch");
            x[field] = temp;
        }

        Debug.printPC("Soha: pc = ");
        assert (length <= 0 ? x[0] == 300 & x[1] == 400 : true);
        assert (length > 0 && field == 0 ? x[0] == 1 && x[1] == 400 : true);
        assert (length > 0 && field == 1 ? x[0] == 300 && x[1] == 1 : true);
        return temp;
    }



    public int arrayStoreTC7(int field, int length) { // should be treated as a new object creation
        int[] x = {300, 400};
        int temp = 1;
        if (length <= 0) {
            //     System.out.println("executing then branch");
            x[field] = 2;
        } else {
            // System.out.println("executing else branch");
            x[field] = temp;
        }

        Debug.printPC("Soha: pc = ");
        assert (length <= 0 && field == 0 ? x[0] == 2 & x[1] == 400 : true);
        assert (length <= 0 && field == 1 ? x[0] == 300 & x[1] == 2 : true);
        assert (length > 0 && field == 0 ? x[0] == 1 && x[1] == 400 : true);
        assert (length > 0 && field == 1 ? x[0] == 300 && x[1] == 1 : true);
        return temp;
    }


    public int getFieldSPFCaseTC1(boolean x){
        TempClass2 tempClass2 = null;
        int y = 0;
        if(x){
            y = tempClass2.tempInt2;
        }
        return y;

    }

    public int arrayLoad0(int field, int length) {
        int[] x = {300, 400};
        int temp = 1;
        try {
            if (length <= 0) {
                temp = 2;
            } else {
                temp = x[field] + 2;
            }
        } catch (ArrayIndexOutOfBoundsException e) {
            temp = 3;
        }
        assert length <= 0 ? temp == 2 : true;
        assert length > 0 && field == 0 ? temp == 302 : true;
        assert length > 0 && field == 1 ? temp == 402 : true;
        assert length > 0 && field != 0 && field != 1 ? temp == 3 : true;
        return temp;
    }*/

/*
    public int branchOnConcrete(boolean x, boolean y) {
        int a = 0;
        if (new TempClass3(true).valid) {
            a = 3;
        } else {
            a = 2;
        }
        return a;
    }


    public int assertRegions(boolean x, boolean y) {
        int a = 0;
        int b = a;
        if (x) {
            a = a+3;
        } else {
            a = a+2;
        }
        assert(x? a == 3 : a==2);
        return a;
    }

    int foo(boolean x) {
        int a;
        if (x) {
            if (x) {
                a = 3;
            } else {
                a = 4;
            }
        } else {
            a = 5;
        }
        return a;
    }
*/




    /*public int segmantTest(int field, int length) throws ArrayIndexOutOfBoundsException {
        int[] x = {300};
        int temp = 1;
        int y = 1;
        if (length >= 0) {
            if (length < 20)
                temp = x[field];
        } else {
            temp = 2;
        }
        return temp;
    }*/

/*

    public int ifNull(String x) {
        if (x == null) {
            System.out.println("x is null");
            return 0;
        } else {
            System.out.println("x is not null");
            return 1;
        }

    }

    public class Silly {
        public int f = 10;
    }

    ;

    void testDynObject(boolean cond, int field) {
        Silly[] arrayOfSilly = {new Silly(), new Silly()};
        int l;
        if (cond) {
            l = arrayOfSilly[field].f;
        }
    }
*/

    /*public int countArrayList(ArrayList<Integer> x) {
        // x = ArrayList of symbolic integers with
        // concrete length
        int sum = 0;
        for (int i = 0; i < x.size(); i++) {
            // Begin region for static unrolling
            if (x.get(i) < 0) sum += -1;
            else if (x.get(i) > 0) sum += 1;
            // End region for static unrolling
        }
        if (sum < 0) System.out.println("neg");
        else if (sum > 0) System.out.println("pos");
        else System.out.println("bug");
        return sum;
    }*/
/*
    int a, b, c, d, e, f;

    public int checkOperator(int a, int b) {
        int ret = -1;
        if (a < b) ret = 1;
        else ret = 0;
        return ret;
    }

    public int cfgTest(int x) {
        int ret = 0;
        while (x >= 0) {
            x--;
            if (x == 0) ret = 1;
            else ret = -1;
            x = x - 1;
        }
        return ret;
    }

    public void testMe4(int[] x, int len, int minusOne, int plusOne) {
        int sum = 0; //Debug.makeSymbolicInteger("sum");
        int temp = 2;
        for (int i = 0; i < len; i++)
            x[i] = Debug.makeSymbolicInteger("x" + i);
        for (int i = 0; i < len; i++) {
            if (x[i] < 0) {
                int temp2 = x[0];
                temp = minusOne;
                sum += temp;
            } else {
                temp = plusOne;
                sum += temp;
            }
        }
        if (sum < 0) System.out.println("neg");
        else if (sum > 0) System.out.println("pos");
        else System.out.println("bug");
    }

    public void testMe5(int[] x, int len) {
        int sum = 0; //Debug.makeSymbolicInteger("sum");
        for (int i = 0; i < len; i++)
            x[i] = Debug.makeSymbolicInteger("x" + i);
        for (int i = 0; i < len; i++) {
            int val = x[i];
            if (val < 0) sum += -1;
            else if (val > 0) sum += 1;
            else sum += 0;
        }
        if (sum < 0) System.out.println("neg");
        else if (sum > 0) System.out.println("pos");
        else System.out.println("bug");
    }


    public int testMe6(int[] x, int len, int minusOne, int plusOne) {
//        int sum = 0; //Debug.makeSymbolicInteger("sum");
//        int temp = 2;
//        for(int i=0; i < len; i++)
//            x[i] = Debug.makeSymbolicInteger("x"+i);
//        int temp2 =0;
//        for (int i = 0; i < len; i++) {
//            if (len < 0) {
//                temp2 = x[minusOne];
//                temp = minusOne;
//                sum += temp;
//            }
//            else {
//                x[0] = 0;
//                temp = plusOne;
//                sum += temp;
//            }
//        }
//        if (sum < 0) {System.out.println("neg"); temp2=x[minusOne];}
//        else if (sum > 0) System.out.println("pos");
//        else System.out.println("bug");
        return 1;
    }

    public void arrayTest(int[] x, int len) {
        for (int i = 0; i < len; i++)
            x[i] = Debug.makeSymbolicInteger("x" + i);
        for (int i = 0; i < len; i++) {
            if (x[i] < 0) x[i] *= -1;
            else x[i] *= 2;
        }
    }*/
/*

    public int irTest1(int x) {
        int y = 0;
        y = x;
        if (x > 0) {
            y = y + 2;
            ++x;
            y = y + 4;
        } else {
            y = y + 5;
        }
        return y;
    }

    public int[] irTest2(int x) {
        int y[] = {300,400};
        int z[] = {200, 300};
        y = z;
        if (x > 0) {
            y[0] = 1;
        } else {
            y[0] = 3;
        }
        y[1] = 5;
        return y;
    }


    public int irTest3(int x) {
        int y[] = {300,400};
        if (x > 0) {
            y[0] = 1;
            y[1] = 2;
        } else {
            y[0] = 3;
            y[1] = 4;
        }
        return x;
    }
*/


    public int irTest5(int x) {
        int y[] = {300,400};
        if (x > 0) {
            y[x] = 1;

        } else {
            y[0] = 3;
        }
        return x;
    }

    public int irTest6(int x) {
        int y;
        if (x > 0) {
            return x;
        } else {
            y = 4;
        }


        return y+5;
    }

    public int fieldTest0(int x) {
        TempClass2 objTemp = new TempClass2();
        int intTemp = 1;

        if (x > 0) {
            intTemp = objTemp.tempInt2 + 4;
        } else {
            intTemp = x + 2;
        }
        return intTemp;
    }


    public int fieldTest00(int x) {
        TempClass2 objTemp = new TempClass2();
        int intTemp = 1;

        if (x > 0) {
            if (x > 10) {
                intTemp = objTemp.tempInt2 + 4;
            }
        } else {
            intTemp = x + 2;
        }
        return intTemp;
    }


    public int fieldTest000(int x) {
        TempClass2 objTemp = new TempClass2();
        int intTemp = 1;
        if (x > 0) {
            intTemp = x + intTemp;
            if (x > 10) {
                intTemp = objTemp.tempInt2 + 4;
            } else {
                intTemp = 5;
            }
        } else {
            intTemp = x + 2;
        }
        return intTemp;
    }


    public int fieldTest0000(int x) {
        TempClass2 objTemp = new TempClass2();
        int intTemp = 1;

        if (x > 0) {
            if (x > 10) {
                intTemp = objTemp.tempInt2 + 4;
            }
        } else {
            if (x < 9)
                intTemp = x + 2;
            else
                intTemp = 9;
        }
        return intTemp;
    }


    public int fieldTest00000(int x) {
        TempClass2 objTemp = new TempClass2();
        int intTemp = 1;

        if (x > 0) {
            if (x > 10) {
                if (x > 20) {
                    intTemp = objTemp.tempInt2 + 4;
                } else {
                    intTemp = 9;
                }
            } else
                intTemp = 11;
        } else {
            if (x < 9)
                intTemp = x + 2;
            else
                intTemp = 9;
        }
        return intTemp;
    }


    public int fieldTest1(int x) {
        TempClass2 temp = new TempClass2();

        if (x > 0) {
            temp.tempInt2 = x + 1;
            temp.tempInt2 = temp.tempInt2 + 4;
        } else {
            temp.tempInt2 = x + 2;
        }
        return temp.tempInt2;
    }


    public int fieldTest2(int x) {
        int temp = 1;
        if (x > 0) {
            temp = x;
            if (x < 5) {
                temp = x + temp;
                temp = temp + 4;
            } else
                temp = x + 3;
        } else {
            temp = x + 2;
        }
        return temp;
    }


    public int fieldTest3(int x) {
        TempClass2 temp = new TempClass2();

        if (x > 0) {
            if (x < 5) {
                temp.tempInt2 = x + 1;
                temp.tempInt2 = temp.tempInt2 + 4;
            } else
                temp.tempInt2 = x + 3;
        } else {
            temp.tempInt2 = x + 2;
        }
        return temp.tempInt2;
    }


    public int fieldTest4(int x) {
        TempClass2 temp = new TempClass2();

        if (temp != null) {
            temp.tempInt2 = x + 1;
            temp.tempInt2 = temp.tempInt2 + 4;
        } else {
            temp.tempInt2 = x + 2;
        }
        return temp.tempInt2;
    }


    public int fieldTest5(int x) {
        int scalarTemp = 1;
        TempClass2 objTemp = new TempClass2();

        if (objTemp != null) {
            scalarTemp = x + 1;
            scalarTemp = scalarTemp + 4;
        } else {
            scalarTemp = x + 2;
        }
        return scalarTemp;
    }

    public int boundedOutRangeloadArrayTC(int index, int length) throws ArrayIndexOutOfBoundsException {
        int[] x = {300};
        int temp = 0;
        int y = 2;
        if (length > 0) {
            try {
                temp = x[index];
            } catch (ArrayIndexOutOfBoundsException e) {
                System.out.println("catch array out of bound");
            }
        } else {
            temp = 2;
        }

        if (temp != 0)
            y = 1;
        else
            y = 0;
        return y;
    }

    public int foo(TempClass2 a1, TempClass2 a2, boolean x) {
        TempClass2 alocal = null;
        if (x)
            alocal.tempInt2 = a1.tempInt2;
        else
            alocal.tempInt2 = a2.tempInt2;
        int r = alocal.tempInt2;
        return r;
    }


    public int foo2(AA a1, AA a2, int x) {
        AA alocal = null;
        if (x > 0)
            alocal.f = a1.f + 1;
        else
            alocal.f = a2.f + 2;

        if(x > 5)
            alocal.f = alocal.f + 3;

        int r = alocal.f;
        return r;
    }

    public int foo3(AA a1, AA a2, int x) {
        AA alocal = null;
        a1.f = 2;
        alocal = a1;

        if (x > 0)
            alocal.f = a2.f + 1;
        else
            a1.f = a2.f + 2;

        int r = alocal.f;
        return r;
    }


    public int foo4(AA a1, AA a2, int x) {
        AA alocal = a1;
        if (x > 0){
            alocal.r.f = a2.f;
        }
        else
            alocal.r.f = 2;

        int r = alocal.r.f;
        return r;
    }

    public int foo5(AA a1, AA a2, int x) {
        AA alocal = null;
        if (x > 0){
            alocal = a2.r;
        }
        else
            alocal = a1.r;

        alocal.r.f = 9;

        int r = alocal.r.f;
        return r;
    }

    public int foo6(AA a1, AA a2, int x) {
        int local;
        AA ref;
        if (x > 0){
            local = a1.f;
        }
        else
            local = a2.f;

        if (x > 5)
            ref = a1.r;
        else
            ref = a2.r;

        ref.f = local;

        return ref.f;
    }

    public int foo7(int x) {
        int ret;
        if (x > 0) {
            ret = x-1;
        } else {
            ret = x+1;
        }
        return ret;
    }


};


class TreeNode {
    TreeNode left;
    TreeNode right;
    int data;

    public static int treeLoad(TreeNode p, int i) {
        if (i < 0 || i >= 2) {
            return 0;
        } else {
            if ((i & 2) != 0)
                p = p.right;
            else
                p = p.left;

            if ((i & 1) != 0)
                p = p.right;
            else
                p = p.left;

            return p.data;
        }
    }
}


class TempClassDerived extends TempClass {

    public static int tempInt = 2; //change this to 2 to test read after write on a class field inside a Veritesting region

    public static int myInt = 1;

    public int getAnotherAnotherTempInt(int a) {
        //TempClass2 t = new TempClass2();
        //t.tempMethod();
        return 1;
    }

    public int getAnotherTempInt(int a) {
        //TempClass2 t = new TempClass2();
        //t.tempMethod();
        //return tempInt;
        return getAnotherAnotherTempInt(TempClassDerived.myInt);
    }

    public int getTempInt(int a) {
        //TempClass2 t = new TempClass2();
        //t.tempMethod();
        //return tempInt;
        return getAnotherTempInt(TempClassDerived.myInt);
    }

    public int getOne(int a) {
        //read-after-write test on tempInt field
        tempInt = a + 1; //LOCAL_INPUT,  FIELD_OUTPUT holes
        a = tempInt + 2; //LOCAL_OUTPUT, FIELD_INPUT holes
        tempInt = a + 3; //LOCAL_INPUT,  FIELD_INPUT holes
        //tempInt = 6 + a;

        //VeritestingPerf.count += 1;
        //return tempInt;
        //return nestedRegion(myInt);
        return getTempInt(tempInt);
        //return 1;
    }

    public int nestedRegion(int x) {
        if (x != 0) {
            if (x != 0) {
                tempInt = 3;
            } else {
                tempInt = 4;
            }
        } else {
            tempInt = 5;
        }
        return tempInt + x;
    }

}

class TempClass {

    public static int tempInt = 1;

    public static int myInt = 1;

    public TempClass() {
        this.tempClass2 = new TempClass2();
    }

    public int getTempInt() {
        return tempInt;
    }

    public int getOne(int a) {
        System.out.println("called TempClass.getOne");
        tempInt = a;
        return tempInt;
    }

    TempClass2 tempClass2;

    public int nestedRegion(int a) {
        return 0;
    }
}

class TempClass2 {

    public int tempInt2 = 1;

    public int tempMethod() {
        return 0;
    }


}

class AA {

    public int f = 1;
    public AA r;

    public int tempMethod() {
        return 0;
    }
}


class TempClass3 {

    public boolean valid;

    public TempClass3(boolean valid) {
        this.valid = valid;
    }
}

/*
  public void collatz(int n) {
    int inter;
    while(n != 1) {
      if( (n & 1) == 1) {
        inter = 3*n + 1;
      } else {
        inter = (n >> 1);
      }
      n = inter;
    }
  }

  public void testMe4 (int[] x, int len) {
    int sum = 0; //Debug.makeSymbolicInteger("sum");
    // for(int i=0; i < len; i++) 
    //   x[i] = Debug.makeSymbolicInteger("x"+i);
    for (int i=0; i < len; i++) {
      if (x[i] < 0) sum += -1;
      else if (x[i] > 0) sum += 1;
    }
    if (sum < 0) System.out.println("neg");
    else if (sum > 0) System.out.println("pos");
    else System.out.println("bug");
  }

  public int gcd(int a, int b) {
    while( a != b ) {
      if ( a > b ) a = a - b;
      else b = b - a;
    }
    return a;
  }



  public int oneBranch(int x) {
    int sum=0;
    if(x < 0) sum += -1;
    else sum += 1;
	return sum;
  }

}*/
