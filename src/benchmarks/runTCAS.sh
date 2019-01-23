#!/bin/bash

alias runSPF-tcas='LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/export/scratch/vaibhav/VeritestingTransformations/lib TARGET_CLASSPATH_WALA=/export/scratch/vaibhav/VeritestingTransformations/build/tcas/ java -Djava.library.path=/export/scratch/vaibhav/VeritestingTransformations/lib -Xmx1024m -ea -Dfile.encoding=UTF-8 -jar /export/scratch/vaibhav/jpf-core-veritesting/build/RunJPF.jar '
shopt -s expand_aliases
VERIDIR=/export/scratch/vaibhav/VeritestingTransformations

# run tcas with 1 step for 4 modes
MAX_STEPS=1 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode1.jpf >& $VERIDIR/logs/tcas.mode1.log
MAX_STEPS=1 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode2.jpf >& $VERIDIR/logs/tcas.mode2.log
MAX_STEPS=1 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode3.jpf >& $VERIDIR/logs/tcas.mode3.log
MAX_STEPS=1 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode4.jpf >& $VERIDIR/logs/tcas.mode4.log

# run tcas with up to 10 steps in mode 4
MAX_STEPS=1 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode4.jpf >& $VERIDIR/logs/tcas.mode4.$(($MAX_STEPS))step.log
MAX_STEPS=2 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode4.jpf >& $VERIDIR/logs/tcas.mode4.$(($MAX_STEPS))step.log
MAX_STEPS=3 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode4.jpf >& $VERIDIR/logs/tcas.mode4.$(($MAX_STEPS))step.log
MAX_STEPS=4 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode4.jpf >& $VERIDIR/logs/tcas.mode4.$(($MAX_STEPS))step.log
MAX_STEPS=5 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode4.jpf >& $VERIDIR/logs/tcas.mode4.$(($MAX_STEPS))step.log
# MAX_STEPS=6 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode4.jpf >& $VERIDIR/logs/tcas.mode4.$(($MAX_STEPS))step.log
# MAX_STEPS=7 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode4.jpf >& $VERIDIR/logs/tcas.mode4.$(($MAX_STEPS))step.log
# MAX_STEPS=8 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode4.jpf >& $VERIDIR/logs/tcas.mode4.$(($MAX_STEPS))step.log
# MAX_STEPS=9 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode4.jpf >& $VERIDIR/logs/tcas.mode4.$(($MAX_STEPS))step.log
# MAX_STEPS=10 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode4.jpf >& $VERIDIR/logs/tcas.mode4.$(($MAX_STEPS))step.log

# run tcas with up to 10 steps in mode 1
MAX_STEPS=1 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode1.jpf >& $VERIDIR/logs/tcas.mode1.$(($MAX_STEPS))step.log
MAX_STEPS=2 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode1.jpf >& $VERIDIR/logs/tcas.mode1.$(($MAX_STEPS))step.log
MAX_STEPS=3 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode1.jpf >& $VERIDIR/logs/tcas.mode1.$(($MAX_STEPS))step.log
MAX_STEPS=4 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode1.jpf >& $VERIDIR/logs/tcas.mode1.$(($MAX_STEPS))step.log
MAX_STEPS=5 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode1.jpf >& $VERIDIR/logs/tcas.mode1.$(($MAX_STEPS))step.log
# MAX_STEPS=6 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode1.jpf >& $VERIDIR/logs/tcas.mode1.$(($MAX_STEPS))step.log
# MAX_STEPS=7 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode1.jpf >& $VERIDIR/logs/tcas.mode1.$(($MAX_STEPS))step.log
# MAX_STEPS=8 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode1.jpf >& $VERIDIR/logs/tcas.mode1.$(($MAX_STEPS))step.log
# MAX_STEPS=9 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode1.jpf >& $VERIDIR/logs/tcas.mode1.$(($MAX_STEPS))step.log
# MAX_STEPS=10 && export MAX_STEPS && runSPF-tcas $VERIDIR/src/tcas/tcas.mode1.jpf >& $VERIDIR/logs/tcas.mode1.$(($MAX_STEPS))step.log

