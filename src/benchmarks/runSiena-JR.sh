#!/bin/bash
alias runSPF-siena='LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/export/scratch2/vaibhav/VeritestingTransformations/lib TARGET_CLASSPATH_WALA=/export/scratch2/vaibhav/VeritestingTransformations/build/siena/ java -Djava.library.path=/export/scratch2/vaibhav/VeritestingTransformations/lib -Xmx8192m -ea -Dfile.encoding=UTF-8 -jar /export/scratch/vaibhav/jpf-core-veritesting/build/RunJPF.jar '

shopt -s expand_aliases
VERIDIR=/export/scratch2/vaibhav/VeritestingTransformations
TIMEOUT_MINS=720 && export TIMEOUT_MINS
LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/export/scratch2/vaibhav/VeritestingTransformations/lib && export LD_LIBRARY_PATH
TARGET_CLASSPATH_WALA=/export/scratch2/vaibhav/VeritestingTransformations/build/siena/ && export TARGET_CLASSPATH_WALA 

for SYM in {5..8}; do 
  for MODE in {2..5}; do
    echo "running siena.$((SYM)).mode$((MODE))";
    timeout $(($TIMEOUT_MINS))m   java -Djava.library.path=/export/scratch2/vaibhav/VeritestingTransformations/lib -Xmx8192m -ea -Dfile.encoding=UTF-8 -jar /export/scratch/vaibhav/jpf-core-veritesting/build/RunJPF.jar $VERIDIR/src/siena/SENPDriver.$((SYM)).mode$((MODE)).jpf >& $VERIDIR/logs/siena.$((SYM)).mode$((MODE)).log 
    if [ $? -eq 124 ]; then 
      echo "running siena.$((SYM)).mode$((MODE)) timed out" >> $VERIDIR/logs/siena.$((SYM)).mode$((MODE)).log
    fi
  done;
done;
