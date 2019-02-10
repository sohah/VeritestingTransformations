#!/bin/bash
alias runSPF-pt='LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/export/scratch2/vaibhav/VeritestingTransformations/lib TARGET_CLASSPATH_WALA=/export/scratch2/vaibhav/VeritestingTransformations/build/printtokens2_3/ java -Djava.library.path=/export/scratch2/vaibhav/VeritestingTransformations/lib -Xmx1024m -ea -Dfile.encoding=UTF-8 -jar /export/scratch/vaibhav/jpf-core-veritesting/build/RunJPF.jar '

shopt -s expand_aliases
VERIDIR=/export/scratch2/vaibhav/VeritestingTransformations
for i in {2..3}; do
  for j in {1..5}; do
    echo "running printtokens2_3.$((i))sym.mode$((j))";
    runSPF-pt $VERIDIR/src/printtokens2_3/printtokens.$((i))sym.mode$((j)).jpf >& $VERIDIR/logs/printtokens.$((i))sym.mode$((j)).log 
  done;
done

