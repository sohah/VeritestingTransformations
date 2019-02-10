#!/bin/bash
alias runSPF-cli='LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/export/scratch2/vaibhav/VeritestingTransformations/lib TARGET_CLASSPATH_WALA=/export/scratch2/vaibhav/VeritestingTransformations/build/apachecli/ java -Djava.library.path=/export/scratch2/vaibhav/VeritestingTransformations/lib -Xmx1024m -ea -Dfile.encoding=UTF-8 -jar /export/scratch/vaibhav/jpf-core-veritesting/build/RunJPF.jar '

shopt -s expand_aliases
VERIDIR=/export/scratch2/vaibhav/VeritestingTransformations
for i in {3..9}; do
  for j in {2..5}; do
    echo "running ApacheCLI.$((i))sym.mode$((j))";
    runSPF-cli $VERIDIR/src/apachecli/ApacheCLI.$((i))sym.mode$((j)).jpf >& $VERIDIR/logs/ApacheCLI.$((i))sym.mode$((j)).log 
  done;
done

for i in {3..7}; do
  for j in {2..5}; do
    echo "running ApacheCLI.$((i))_1sym.mode$((j))";
    runSPF-cli $VERIDIR/src/apachecli/ApacheCLI.$((i))_1sym.mode$((j)).jpf >& $VERIDIR/logs/ApacheCLI.$((i))_1sym.mode$((j)).log 
  done;
done

