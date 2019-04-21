#!/bin/bash

alias runSPF='LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/export/scratch2/vaibhav/VeritestingTransformations/lib TARGET_CLASSPATH_WALA=/export/scratch2/vaibhav/VeritestingTransformations/build/replace/ java -Djava.library.path=/export/scratch2/vaibhav/VeritestingTransformations/lib -Xmx8192m -ea -Dfile.encoding=UTF-8 -jar /export/scratch/vaibhav/jpf-core-veritesting/build/RunJPF.jar '
shopt -s expand_aliases
VERIDIR=/export/scratch2/vaibhav/VeritestingTransformations

runSPF $VERIDIR/src/replace/ReplaceEqCheck.jpf >& $VERIDIR/logs/ReplaceEqCheck.log
