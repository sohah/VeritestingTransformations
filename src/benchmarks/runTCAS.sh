#!/bin/bash

alias runSPF-tcas='LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/export/scratch/vaibhav/VeritestingTransformations/lib TARGET_CLASSPATH_WALA=/export/scratch/vaibhav/VeritestingTransformations/build/tcas/ java -Djava.library.path=/export/scratch/vaibhav/VeritestingTransformations/lib -Xmx1024m -ea -Dfile.encoding=UTF-8 -jar /export/scratch/vaibhav/jpf-core-veritesting/build/RunJPF.jar '
shopt -s expand_aliases
VERIDIR=/export/scratch2/vaibhav/VeritestingTransformations

# run tcas with 1 step for 5 modes
MAX_STEPS=1 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode1.jpf >& $VERIDIR/logs/tcas.mode1.log
MAX_STEPS=1 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode2.jpf >& $VERIDIR/logs/tcas.mode2.log
MAX_STEPS=1 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode3.jpf >& $VERIDIR/logs/tcas.mode3.log
MAX_STEPS=1 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode4.jpf >& $VERIDIR/logs/tcas.mode4.log
MAX_STEPS=1 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode4.jpf >& $VERIDIR/logs/tcas.mode4.log
MAX_STEPS=1 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode5.jpf >& $VERIDIR/logs/tcas.mode5.log

# run tcas with up to 10 steps in mode 5
echo "Running 1 step - mode 5"
MAX_STEPS=1 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode5.jpf >& $VERIDIR/logs/tcas.mode5.$(($MAX_STEPS))step.log
echo "Running 2 step - mode 5"
MAX_STEPS=2 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode5.jpf >& $VERIDIR/logs/tcas.mode5.$(($MAX_STEPS))step.log
echo "Running 3 step - mode 5"
MAX_STEPS=3 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode5.jpf >& $VERIDIR/logs/tcas.mode5.$(($MAX_STEPS))step.log
echo "Running 4 step - mode 5"
MAX_STEPS=4 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode5.jpf >& $VERIDIR/logs/tcas.mode5.$(($MAX_STEPS))step.log
echo "Running 5 step - mode 5"
MAX_STEPS=5 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode5.jpf >& $VERIDIR/logs/tcas.mode5.$(($MAX_STEPS))step.log
echo "Running 6 step - mode 5"
MAX_STEPS=6 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode5.jpf >& $VERIDIR/logs/tcas.mode5.$(($MAX_STEPS))step.log
echo "Running 7 step - mode 5"
MAX_STEPS=7 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode5.jpf >& $VERIDIR/logs/tcas.mode5.$(($MAX_STEPS))step.log
echo "Running 8 step - mode 5"
MAX_STEPS=8 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode5.jpf >& $VERIDIR/logs/tcas.mode5.$(($MAX_STEPS))step.log
echo "Running 9 step - mode 5"
MAX_STEPS=9 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode5.jpf >& $VERIDIR/logs/tcas.mode5.$(($MAX_STEPS))step.log
echo "Running 10 step - mode 5"
MAX_STEPS=10 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode5.jpf >& $VERIDIR/logs/tcas.mode5.$(($MAX_STEPS))step.log

# run tcas with up to 10 steps in mode 1
echo "Running 1 step - mode 1"
MAX_STEPS=1 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode1.jpf >& $VERIDIR/logs/tcas.mode1.$(($MAX_STEPS))step.log
echo "Running 2 step - mode 1"
MAX_STEPS=2 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode1.jpf >& $VERIDIR/logs/tcas.mode1.$(($MAX_STEPS))step.log
echo "Running 3 step - mode 1"
MAX_STEPS=3 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode1.jpf >& $VERIDIR/logs/tcas.mode1.$(($MAX_STEPS))step.log
echo "Running 4 step - mode 1"
MAX_STEPS=4 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode1.jpf >& $VERIDIR/logs/tcas.mode1.$(($MAX_STEPS))step.log
echo "Running 5 step - mode 1"
MAX_STEPS=5 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode1.jpf >& $VERIDIR/logs/tcas.mode1.$(($MAX_STEPS))step.log
echo "Running 6 step - mode 1"
MAX_STEPS=6 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode1.jpf >& $VERIDIR/logs/tcas.mode1.$(($MAX_STEPS))step.log
echo "Running 7 step - mode 1"
MAX_STEPS=7 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode1.jpf >& $VERIDIR/logs/tcas.mode1.$(($MAX_STEPS))step.log
echo "Running 8 step - mode 1"
MAX_STEPS=8 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode1.jpf >& $VERIDIR/logs/tcas.mode1.$(($MAX_STEPS))step.log
echo "Running 9 step - mode 1"
MAX_STEPS=9 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode1.jpf >& $VERIDIR/logs/tcas.mode1.$(($MAX_STEPS))step.log
echo "Running 10 step - mode 1"
MAX_STEPS=10 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode1.jpf >& $VERIDIR/logs/tcas.mode1.$(($MAX_STEPS))step.log

