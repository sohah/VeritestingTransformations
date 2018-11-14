#!/bin/bash

alias runSPF-wbs='LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/export/scratch/vaibhav/VeritestingTransformations/lib TARGET_CLASSPATH_WALA=/export/scratch/vaibhav/VeritestingTransformations/build/wbs/ java -Djava.library.path=/export/scratch/vaibhav/VeritestingTransformations/lib -Xmx1024m -ea -Dfile.encoding=UTF-8 -jar /export/scratch/vaibhav/jpf-core-veritesting/build/RunJPF.jar '
shopt -s expand_aliases
VERIDIR=/export/scratch/vaibhav/VeritestingTransformations
runSPF-wbs $VERIDIR/src/wbs/WBS.mode1.jpf >& $VERIDIR/logs/WBS.mode1.log
runSPF-wbs $VERIDIR/src/wbs/WBS.mode2.jpf >& $VERIDIR/logs/WBS.mode2.log
runSPF-wbs $VERIDIR/src/wbs/WBS.mode3.jpf >& $VERIDIR/logs/WBS.mode3.log
runSPF-wbs $VERIDIR/src/wbs/WBS.mode4.jpf >& $VERIDIR/logs/WBS.mode4.log

# runSPF $VERIDIR/src/examples/tcas_singlereturn.mode1.jpf >& $VERIDIR/logs/tcas_singlereturn.mode1.log
# runSPF $VERIDIR/src/examples/tcas_singlereturn.mode2.jpf >& $VERIDIR/logs/tcas_singlereturn.mode2.log
# runSPF $VERIDIR/src/examples/tcas_singlereturn.mode3.jpf >& $VERIDIR/logs/tcas_singlereturn.mode3.log
# runSPF $VERIDIR/src/examples/tcas_singlereturn.mode4.jpf >& $VERIDIR/logs/tcas_singlereturn.mode4.log

# runSPF $VERIDIR/src/examples/replace.mode1.jpf >& $VERIDIR/logs/replace.mode1.log
# runSPF $VERIDIR/src/examples/replace.mode2.jpf >& $VERIDIR/logs/replace.mode2.log
# runSPF $VERIDIR/src/examples/replace.mode3.jpf >& $VERIDIR/logs/replace.mode3.log
# runSPF $VERIDIR/src/examples/replace.mode4.jpf >& $VERIDIR/logs/replace.mode4.log

MAX_STEPS=1 && export MAX_STEPS && runSPF-wbs $VERIDIR/src/wbs/RunWBS.mode4.jpf |& tee logs/RunWBS.mode4.$(($MAX_STEPS))step.log
MAX_STEPS=2 && export MAX_STEPS && runSPF-wbs $VERIDIR/src/wbs/RunWBS.mode4.jpf |& tee logs/RunWBS.mode4.$(($MAX_STEPS))step.log
MAX_STEPS=3 && export MAX_STEPS && runSPF-wbs $VERIDIR/src/wbs/RunWBS.mode4.jpf |& tee logs/RunWBS.mode4.$(($MAX_STEPS))step.log
MAX_STEPS=4 && export MAX_STEPS && runSPF-wbs $VERIDIR/src/wbs/RunWBS.mode4.jpf |& tee logs/RunWBS.mode4.$(($MAX_STEPS))step.log
MAX_STEPS=5 && export MAX_STEPS && runSPF-wbs $VERIDIR/src/wbs/RunWBS.mode4.jpf |& tee logs/RunWBS.mode4.$(($MAX_STEPS))step.log
