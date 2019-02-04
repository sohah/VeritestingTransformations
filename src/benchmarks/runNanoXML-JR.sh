#!/bin/bash
alias runSPF-nanoxml='LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/export/scratch2/vaibhav/VeritestingTransformations/lib TARGET_CLASSPATH_WALA=/export/scratch2/vaibhav/VeritestingTransformations/build/nanoxml/ java -Djava.library.path=/export/scratch2/vaibhav/VeritestingTransformations/lib -Xmx1024m -ea -Dfile.encoding=UTF-8 -jar /export/scratch/vaibhav/jpf-core-veritesting/build/RunJPF.jar '

shopt -s expand_aliases
VERIDIR=/export/scratch2/vaibhav/VeritestingTransformations
for i in {5..9}; do
  for j in {2..5}; do
    echo "running DumpXML.$((i))sym.mode$((j))";
    runSPF-nanoxml  $VERIDIR/src/nanoxml/DumpXML.$((i))sym.mode$((j)).jpf >& $VERIDIR/logs/DumpXML.$((i))sym.mode$((j)).log 
  done;
done

