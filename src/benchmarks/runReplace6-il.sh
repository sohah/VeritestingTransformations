#!/bin/bash

alias runSPF='LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/export/scratch/vaibhav/VeritestingTransformations/lib TARGET_CLASSPATH_WALA=/export/scratch/vaibhav/VeritestingTransformations/build/examples/ java -Djava.library.path=/export/scratch/vaibhav/VeritestingTransformations/lib -Xmx1024m -ea -Dfile.encoding=UTF-8 -jar /export/scratch/vaibhav/jpf-core-veritesting/build/RunJPF.jar '
shopt -s expand_aliases
VERIDIR=/export/scratch/vaibhav/VeritestingTransformations

echo -e "replace6.mode3.il10\n"
runSPF $VERIDIR/src/examples/replace6.mode3.il10.jpf >& $VERIDIR/logs/replace6.mode3.il10.log
echo -e "replace6.mode3.il100\n"
runSPF $VERIDIR/src/examples/replace6.mode3.il100.jpf >& $VERIDIR/logs/replace6.mode3.il100.log
echo -e "replace6.mode3.il1000\n"
runSPF $VERIDIR/src/examples/replace6.mode3.il1000.jpf >& $VERIDIR/logs/replace6.mode3.il1000.log
echo -e "replace6.mode3.il10000\n"
runSPF $VERIDIR/src/examples/replace6.mode3.il10000.jpf >& $VERIDIR/logs/replace6.mode3.il10000.log
echo -e "replace6.mode3.il15000\n"
runSPF $VERIDIR/src/examples/replace6.mode3.il15000.jpf >& $VERIDIR/logs/replace6.mode3.il15000.log
echo -e "replace6.mode3.il20000\n"
runSPF $VERIDIR/src/examples/replace6.mode3.il20000.jpf >& $VERIDIR/logs/replace6.mode3.il20000.log
echo -e "replace6.mode3.il25000\n"
runSPF $VERIDIR/src/examples/replace6.mode3.il25000.jpf >& $VERIDIR/logs/replace6.mode3.il25000.log
echo -e "replace6.mode3.il30000\n"
runSPF $VERIDIR/src/examples/replace6.mode3.il30000.jpf >& $VERIDIR/logs/replace6.mode3.il30000.log
