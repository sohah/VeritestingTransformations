#!/bin/bash
alias runSPF-merarbiter-v2='LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/export/scratch2/vaibhav/VeritestingTransformations/lib TARGET_CLASSPATH_WALA=/export/scratch2/vaibhav/VeritestingTransformations/build/merarbiter-v2/ java -Djava.library.path=/export/scratch2/vaibhav/VeritestingTransformations/lib -Xmx8192m -ea -Dfile.encoding=UTF-8 -jar /export/scratch/vaibhav/jpf-core-veritesting/build/RunJPF.jar '

shopt -s expand_aliases
VERIDIR=/export/scratch2/vaibhav/VeritestingTransformations
TIMEOUT_MINS=720 && export TIMEOUT_MINS
LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/export/scratch2/vaibhav/VeritestingTransformations/lib && export LD_LIBRARY_PATH
TARGET_CLASSPATH_WALA=/export/scratch2/vaibhav/VeritestingTransformations/build/merarbiter-v2/ && export TARGET_CLASSPATH_WALA 

MODE=4 && export MODE
for STEPS in {6..7}; do
  #for MODE in {5..5}; do
    echo "running MerArbiter-v2.$((STEPS))step.mode$((MODE))";
    MAX_STEPS=$(($STEPS)) && export MAX_STEPS 
    timeout $(($TIMEOUT_MINS))m   java -Djava.library.path=/export/scratch2/vaibhav/VeritestingTransformations/lib -Xmx8192m -ea -Dfile.encoding=UTF-8 -jar /export/scratch/vaibhav/jpf-core-veritesting/build/RunJPF.jar $VERIDIR/src/MerArbiter-v2/merarbiterSPF.mode$((MODE)).jpf >& $VERIDIR/logs/merarbiter.$((STEPS))step.mode$((MODE)).log 
    if [ $? -eq 124 ]; then 
      echo "running MerArbiter-v2.$((STEPS))step.mode$((MODE)) timed out" >> $VERIDIR/logs/merarbiter.$((STEPS))step.mode$((MODE)).log
    fi
  #done;
done

