#!/bin/bash
alias runSPF-merarbiter-v2='LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/export/scratch2/vaibhav/VeritestingTransformations/lib TARGET_CLASSPATH_WALA=/export/scratch2/vaibhav/VeritestingTransformations/build/merarbiter-v2/ java -Djava.library.path=/export/scratch2/vaibhav/VeritestingTransformations/lib -Xmx1024m -ea -Dfile.encoding=UTF-8 -jar /export/scratch/vaibhav/jpf-core-veritesting/build/RunJPF.jar '

shopt -s expand_aliases
VERIDIR=/export/scratch2/vaibhav/VeritestingTransformations
for i in {2..8}; do
  for j in {2..5}; do
    echo "running MerArbiter-v2.$((i))step.mode$((j))";
    MAX_STEPS=$(($i)) && export MAX_STEPS && runSPF-merarbiter-v2  $VERIDIR/src/MerArbiter-v2/merarbiterSPF.mode$((j)).jpf >& $VERIDIR/logs/merarbiter.$((i))step.mode$((j)).log 
  done;
done

