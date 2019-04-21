#!/bin/bash

alias runSPF-tcas='LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/export/scratch2/vaibhav/VeritestingTransformations/lib TARGET_CLASSPATH_WALA=/export/scratch2/vaibhav/VeritestingTransformations/build/tcas/ java -Djava.library.path=/export/scratch2/vaibhav/VeritestingTransformations/lib -Xmx8192m -ea -Dfile.encoding=UTF-8 -jar /export/scratch/vaibhav/jpf-core-veritesting/build/RunJPF.jar '
shopt -s expand_aliases
VERIDIR=/export/scratch2/vaibhav/VeritestingTransformations
# TCASEqCheck should not be using a specific number of steps, it should always perform equivalence-checking over TCAS using only one step
unset MAX_STEPS
runSPF-tcas $VERIDIR/src/tcas/TCASEqCheck.jpf >& $VERIDIR/logs/TCASEqCheck.log
