#!/bin/bash
alias runSPF-nanoxml='LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/export/scratch2/vaibhav/VeritestingTransformations/lib TARGET_CLASSPATH_WALA=/export/scratch2/vaibhav/VeritestingTransformations/build/nanoxml/ java -Djava.library.path=/export/scratch2/vaibhav/VeritestingTransformations/lib -Xmx8192m -ea -Dfile.encoding=UTF-8 -jar /export/scratch/vaibhav/jpf-core-veritesting/build/RunJPF.jar '
shopt -s direxpand
shopt -s expand_aliases
VERIDIR=/export/scratch2/vaibhav/VeritestingTransformations
# for i in {5..8}; do
#   for j in {5..2}; do
#     echo "running DumpXML.$((i))sym.mode$((j))";
#     runSPF-nanoxml  $VERIDIR/src/nanoxml/DumpXML.$((i))sym.mode$((j)).jpf >& $VERIDIR/logs/DumpXML.$((i))sym.mode$((j)).log 
#   done;
# done
# 
# for i in {9..9}; do
#   for j in {5..2}; do
#     echo "running DumpXML.$((i))sym.mode$((j))";
#     runSPF-nanoxml  $VERIDIR/src/nanoxml/DumpXML.$((i))sym.mode$((j)).jpf >& $VERIDIR/logs/DumpXML.$((i))sym.mode$((j)).log 
#   done;
# done
TIMEOUT_MINS=720 && export TIMEOUT_MINS
LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/export/scratch2/vaibhav/VeritestingTransformations/lib && export LD_LIBRARY_PATH
TARGET_CLASSPATH_WALA=/export/scratch2/vaibhav/VeritestingTransformations/build/nanoxml/ && export TARGET_CLASSPATH_WALA

for NSYM in {7..7}; do
  for MODE in {5..2}; do
    echo "running DumpXML.$(($NSYM))sym.mode$(($MODE))" && timeout $(($TIMEOUT_MINS))m  java -Djava.library.path=/export/scratch2/vaibhav/VeritestingTransformations/lib -Xmx8192m -ea -Dfile.encoding=UTF-8 -jar /export/scratch/vaibhav/jpf-core-veritesting/build/RunJPF.jar   $VERIDIR/src/nanoxml/DumpXML.$(($NSYM))sym.mode$(($MODE)).jpf >& $VERIDIR/logs/DumpXML.$((NSYM))sym.mode$((MODE)).log 
    if [ $? -eq 124 ]; then 
          echo "running DumpXML.$(($NSYM))sym.mode$(($MODE)) timed out" >> $VERIDIR/logs/DumpXML.$((NSYM))sym.mode$((MODE)).log
    fi
  done;
done

NSYM=8
MODE=5
#for NSYM in {8..8}; do
#  for MODE in {5..5}; do
    echo "running DumpXML.$(($NSYM))sym.mode$(($MODE))" && timeout $(($TIMEOUT_MINS))m  java -Djava.library.path=/export/scratch2/vaibhav/VeritestingTransformations/lib -Xmx8192m -ea -Dfile.encoding=UTF-8 -jar /export/scratch/vaibhav/jpf-core-veritesting/build/RunJPF.jar   $VERIDIR/src/nanoxml/DumpXML.$(($NSYM))sym.mode$(($MODE)).jpf >& $VERIDIR/logs/DumpXML.$((NSYM))sym.mode$((MODE)).log 
    if [ $? -eq 124 ]; then 
          echo "running DumpXML.$(($NSYM))sym.mode$(($MODE)) timed out" >> $VERIDIR/logs/DumpXML.$((NSYM))sym.mode$((MODE)).log
    fi
#  done;
#done
