#!/bin/bash

alias runSPF-tcas-sr='LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/export/scratch/vaibhav/VeritestingTransformations/lib TARGET_CLASSPATH_WALA=/export/scratch/vaibhav/VeritestingTransformations/build/tcas_sr/ java -Djava.library.path=/export/scratch/vaibhav/VeritestingTransformations/lib -Xmx1024m -ea -Dfile.encoding=UTF-8 -jar /export/scratch/vaibhav/jpf-core-veritesting/build/RunJPF.jar '
shopt -s expand_aliases
VERIDIR=/export/scratch/vaibhav/VeritestingTransformations

# run tcas-singlereturn with 1 step for 4 modes
MAX_STEPS=1 && export MAX_STEPS && runSPF-tcas-sr $VERIDIR/src/tcas_sr/tcas_singlereturn.mode1.jpf >& $VERIDIR/logs/tcas_singlereturn.mode1.log
MAX_STEPS=1 && export MAX_STEPS && runSPF-tcas-sr $VERIDIR/src/tcas_sr/tcas_singlereturn.mode2.jpf >& $VERIDIR/logs/tcas_singlereturn.mode2.log
MAX_STEPS=1 && export MAX_STEPS && runSPF-tcas-sr $VERIDIR/src/tcas_sr/tcas_singlereturn.mode3.jpf >& $VERIDIR/logs/tcas_singlereturn.mode3.log
MAX_STEPS=1 && export MAX_STEPS && runSPF-tcas-sr $VERIDIR/src/tcas_sr/tcas_singlereturn.mode4.jpf >& $VERIDIR/logs/tcas_singlereturn.mode4.log

# run tcas-singlereturn with up to 10 steps in mode 4
MAX_STEPS=1 && export MAX_STEPS && runSPF-tcas-sr $VERIDIR/src/tcas_sr/tcas_singlereturn.mode4.jpf >& $VERIDIR/logs/tcas_singlereturn.mode4.$(($MAX_STEPS))step.log
MAX_STEPS=2 && export MAX_STEPS && runSPF-tcas-sr $VERIDIR/src/tcas_sr/tcas_singlereturn.mode4.jpf >& $VERIDIR/logs/tcas_singlereturn.mode4.$(($MAX_STEPS))step.log
MAX_STEPS=3 && export MAX_STEPS && runSPF-tcas-sr $VERIDIR/src/tcas_sr/tcas_singlereturn.mode4.jpf >& $VERIDIR/logs/tcas_singlereturn.mode4.$(($MAX_STEPS))step.log
MAX_STEPS=4 && export MAX_STEPS && runSPF-tcas-sr $VERIDIR/src/tcas_sr/tcas_singlereturn.mode4.jpf >& $VERIDIR/logs/tcas_singlereturn.mode4.$(($MAX_STEPS))step.log
MAX_STEPS=5 && export MAX_STEPS && runSPF-tcas-sr $VERIDIR/src/tcas_sr/tcas_singlereturn.mode4.jpf >& $VERIDIR/logs/tcas_singlereturn.mode4.$(($MAX_STEPS))step.log
MAX_STEPS=6 && export MAX_STEPS && runSPF-tcas-sr $VERIDIR/src/tcas_sr/tcas_singlereturn.mode4.jpf >& $VERIDIR/logs/tcas_singlereturn.mode4.$(($MAX_STEPS))step.log
MAX_STEPS=7 && export MAX_STEPS && runSPF-tcas-sr $VERIDIR/src/tcas_sr/tcas_singlereturn.mode4.jpf >& $VERIDIR/logs/tcas_singlereturn.mode4.$(($MAX_STEPS))step.log
MAX_STEPS=8 && export MAX_STEPS && runSPF-tcas-sr $VERIDIR/src/tcas_sr/tcas_singlereturn.mode4.jpf >& $VERIDIR/logs/tcas_singlereturn.mode4.$(($MAX_STEPS))step.log
MAX_STEPS=9 && export MAX_STEPS && runSPF-tcas-sr $VERIDIR/src/tcas_sr/tcas_singlereturn.mode4.jpf >& $VERIDIR/logs/tcas_singlereturn.mode4.$(($MAX_STEPS))step.log
MAX_STEPS=10 && export MAX_STEPS && runSPF-tcas-sr $VERIDIR/src/tcas_sr/tcas_singlereturn.mode4.jpf >& $VERIDIR/logs/tcas_singlereturn.mode4.$(($MAX_STEPS))step.log

# run tcas-singlereturn with up to 10 steps in mode 1
MAX_STEPS=1 && export MAX_STEPS && runSPF-tcas-sr $VERIDIR/src/tcas_sr/tcas_singlereturn.mode1.jpf >& $VERIDIR/logs/tcas_singlereturn.mode1.$(($MAX_STEPS))step.log
MAX_STEPS=2 && export MAX_STEPS && runSPF-tcas-sr $VERIDIR/src/tcas_sr/tcas_singlereturn.mode1.jpf >& $VERIDIR/logs/tcas_singlereturn.mode1.$(($MAX_STEPS))step.log
MAX_STEPS=3 && export MAX_STEPS && runSPF-tcas-sr $VERIDIR/src/tcas_sr/tcas_singlereturn.mode1.jpf >& $VERIDIR/logs/tcas_singlereturn.mode1.$(($MAX_STEPS))step.log
MAX_STEPS=4 && export MAX_STEPS && runSPF-tcas-sr $VERIDIR/src/tcas_sr/tcas_singlereturn.mode1.jpf >& $VERIDIR/logs/tcas_singlereturn.mode1.$(($MAX_STEPS))step.log
MAX_STEPS=5 && export MAX_STEPS && runSPF-tcas-sr $VERIDIR/src/tcas_sr/tcas_singlereturn.mode1.jpf >& $VERIDIR/logs/tcas_singlereturn.mode1.$(($MAX_STEPS))step.log
MAX_STEPS=6 && export MAX_STEPS && runSPF-tcas-sr $VERIDIR/src/tcas_sr/tcas_singlereturn.mode1.jpf >& $VERIDIR/logs/tcas_singlereturn.mode1.$(($MAX_STEPS))step.log
MAX_STEPS=7 && export MAX_STEPS && runSPF-tcas-sr $VERIDIR/src/tcas_sr/tcas_singlereturn.mode1.jpf >& $VERIDIR/logs/tcas_singlereturn.mode1.$(($MAX_STEPS))step.log
MAX_STEPS=8 && export MAX_STEPS && runSPF-tcas-sr $VERIDIR/src/tcas_sr/tcas_singlereturn.mode1.jpf >& $VERIDIR/logs/tcas_singlereturn.mode1.$(($MAX_STEPS))step.log
MAX_STEPS=9 && export MAX_STEPS && runSPF-tcas-sr $VERIDIR/src/tcas_sr/tcas_singlereturn.mode1.jpf >& $VERIDIR/logs/tcas_singlereturn.mode1.$(($MAX_STEPS))step.log
MAX_STEPS=10 && export MAX_STEPS && runSPF-tcas-sr $VERIDIR/src/tcas_sr/tcas_singlereturn.mode1.jpf >& $VERIDIR/logs/tcas_singlereturn.mode1.$(($MAX_STEPS))step.log

