#!/bin/bash

alias runSPF='LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/export/scratch/vaibhav/VeritestingTransformations/lib TARGET_CLASSPATH_WALA=/export/scratch/vaibhav/VeritestingTransformations/build/examples/ java -Djava.library.path=/export/scratch/vaibhav/VeritestingTransformations/lib -Xmx1024m -ea -Dfile.encoding=UTF-8 -jar /export/scratch/vaibhav/jpf-core-veritesting/build/RunJPF.jar '
shopt -s expand_aliases
VERIDIR=/export/scratch/vaibhav/VeritestingTransformations

runSPF $VERIDIR/src/examples/replace11.mode3.jpf >& $VERIDIR/logs/replace11.mode3.log
runSPF $VERIDIR/src/examples/replace11.mode2.jpf >& $VERIDIR/logs/replace11.mode2.log
runSPF $VERIDIR/src/examples/replace11.mode1.jpf >& $VERIDIR/logs/replace11.mode1.log
runSPF $VERIDIR/src/examples/replace11.mode4.jpf >& $VERIDIR/logs/replace11.mode4.log
