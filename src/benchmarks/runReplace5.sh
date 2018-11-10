#!/bin/bash

alias runSPF='LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/export/scratch/vaibhav/VeritestingTransformations/lib TARGET_CLASSPATH_WALA=/export/scratch/vaibhav/VeritestingTransformations/build/examples/ java -Djava.library.path=/export/scratch/vaibhav/VeritestingTransformations/lib -Xmx1024m -ea -Dfile.encoding=UTF-8 -jar /export/scratch/vaibhav/jpf-core-veritesting/build/RunJPF.jar '
shopt -s expand_aliases
VERIDIR=/export/scratch/vaibhav/VeritestingTransformations

runSPF $VERIDIR/src/examples/replace.mode1.jpf >& $VERIDIR/logs/replace.mode1.log
runSPF $VERIDIR/src/examples/replace.mode2.jpf >& $VERIDIR/logs/replace.mode2.log
runSPF $VERIDIR/src/examples/replace.mode3.jpf >& $VERIDIR/logs/replace.mode3.log
runSPF $VERIDIR/src/examples/replace.mode4.jpf >& $VERIDIR/logs/replace.mode4.log

runSPF $VERIDIR/src/examples/replace_sr.jpf >& $VERIDIR/logs/replace_sr.mode3.log
