import edu.umn.crisys.plexil.java.plx.CommandHandle;
import edu.umn.crisys.plexil.java.plx.JavaPlan;
import edu.umn.crisys.plexil.java.plx.SimpleCurrentNext;
import edu.umn.crisys.plexil.java.plx.Variable;
import edu.umn.crisys.plexil.java.values.BooleanValue;
import edu.umn.crisys.plexil.java.values.IntegerValue;
import edu.umn.crisys.plexil.java.values.NodeFailureType;
import edu.umn.crisys.plexil.java.values.NodeOutcome;
import edu.umn.crisys.plexil.java.values.NodeState;
import edu.umn.crisys.plexil.java.values.PBoolean;
import edu.umn.crisys.plexil.java.values.PNumeric;
import edu.umn.crisys.plexil.java.values.PValue;
import edu.umn.crisys.plexil.java.values.RealValue;
import edu.umn.crisys.plexil.java.values.StringValue;

public class TargetPanorama
    extends JavaPlan
{

    private Variable<PBoolean> DriveToTarget__drive_done = new Variable<PBoolean>("DriveToTarget/drive_done", BooleanValue.get((false)));
    private Variable<NodeOutcome> DriveToTarget__StopForTimeout__Stop__Stop__outcome = new Variable<NodeOutcome>("DriveToTarget__StopForTimeout__Stop/Stop.outcome", NodeOutcome.UNKNOWN);
    private Variable<NodeFailureType> DriveToTarget__StopForTarget__SetDriveFlag__SetDriveFlag__failure = new Variable<NodeFailureType>("DriveToTarget__StopForTarget__SetDriveFlag/SetDriveFlag.failure", NodeFailureType.UNKNOWN);
    private Variable<NodeOutcome> DriveToTarget__StopForTarget__SetDriveFlag__SetDriveFlag__outcome = new Variable<NodeOutcome>("DriveToTarget__StopForTarget__SetDriveFlag/SetDriveFlag.outcome", NodeOutcome.UNKNOWN);
    private Variable<NodeFailureType> DriveToTarget__StopForTimeout__Stop__Stop__failure = new Variable<NodeFailureType>("DriveToTarget__StopForTimeout__Stop/Stop.failure", NodeFailureType.UNKNOWN);
    public CommandHandle DriveToTarget__TakePancam__command_handle = new CommandHandle();
    private Variable<NodeOutcome> DriveToTarget__StopForTimeout__SetTimeoutFlag__SetTimeoutFlag__outcome = new Variable<NodeOutcome>("DriveToTarget__StopForTimeout__SetTimeoutFlag/SetTimeoutFlag.outcome", NodeOutcome.UNKNOWN);
    private Variable<NodeOutcome> DriveToTarget__StopForTarget__StopForTarget__outcome = new Variable<NodeOutcome>("DriveToTarget__StopForTarget/StopForTarget.outcome", NodeOutcome.UNKNOWN);
    public CommandHandle DriveToTarget__StopForTarget__Stop__command_handle = new CommandHandle();
    private PValue PREV_VALUE___DriveToTarget__StopForTimeout__SetTimeoutFlag;
    private Variable<NodeFailureType> DriveToTarget__TakePancam__TakePancam__failure = new Variable<NodeFailureType>("DriveToTarget__TakePancam/TakePancam.failure", NodeFailureType.UNKNOWN);
    private PValue PREV_VALUE___DriveToTarget__StopForTarget__SetDriveFlag;
    private Variable<NodeFailureType> DriveToTarget__StopForTarget__StopForTarget__failure = new Variable<NodeFailureType>("DriveToTarget__StopForTarget/StopForTarget.failure", NodeFailureType.UNKNOWN);
    private Variable<NodeOutcome> DriveToTarget__TakeNavcam__TakeNavcam__outcome = new Variable<NodeOutcome>("DriveToTarget__TakeNavcam/TakeNavcam.outcome", NodeOutcome.UNKNOWN);
    private Variable<NodeFailureType> DriveToTarget__StopForTimeout__StopForTimeout__failure = new Variable<NodeFailureType>("DriveToTarget__StopForTimeout/StopForTimeout.failure", NodeFailureType.UNKNOWN);
    private Variable<NodeFailureType> DriveToTarget__DriveToTarget__failure = new Variable<NodeFailureType>("DriveToTarget/DriveToTarget.failure", NodeFailureType.UNKNOWN);
    private Variable<NodeFailureType> DriveToTarget__StopForTimeout__SetTimeoutFlag__SetTimeoutFlag__failure = new Variable<NodeFailureType>("DriveToTarget__StopForTimeout__SetTimeoutFlag/SetTimeoutFlag.failure", NodeFailureType.UNKNOWN);
    public CommandHandle DriveToTarget__TakeNavcam__command_handle = new CommandHandle();
    private Variable<NodeFailureType> DriveToTarget__StopForTarget__Stop__Stop__failure = new Variable<NodeFailureType>("DriveToTarget__StopForTarget__Stop/Stop.failure", NodeFailureType.UNKNOWN);
    public CommandHandle DriveToTarget__Drive__command_handle = new CommandHandle();
    private Variable<NodeOutcome> DriveToTarget__DriveToTarget__outcome = new Variable<NodeOutcome>("DriveToTarget/DriveToTarget.outcome", NodeOutcome.UNKNOWN);
    private Variable<NodeOutcome> DriveToTarget__StopForTarget__Stop__Stop__outcome = new Variable<NodeOutcome>("DriveToTarget__StopForTarget__Stop/Stop.outcome", NodeOutcome.UNKNOWN);
    private Variable<NodeOutcome> DriveToTarget__TakePancam__TakePancam__outcome = new Variable<NodeOutcome>("DriveToTarget__TakePancam/TakePancam.outcome", NodeOutcome.UNKNOWN);
    private Variable<NodeOutcome> DriveToTarget__Drive__Drive__outcome = new Variable<NodeOutcome>("DriveToTarget__Drive/Drive.outcome", NodeOutcome.UNKNOWN);
    private Variable<NodeFailureType> DriveToTarget__TakeNavcam__TakeNavcam__failure = new Variable<NodeFailureType>("DriveToTarget__TakeNavcam/TakeNavcam.failure", NodeFailureType.UNKNOWN);
    private Variable<NodeOutcome> DriveToTarget__StopForTimeout__StopForTimeout__outcome = new Variable<NodeOutcome>("DriveToTarget__StopForTimeout/StopForTimeout.outcome", NodeOutcome.UNKNOWN);
    public CommandHandle DriveToTarget__StopForTimeout__Stop__command_handle = new CommandHandle();
    private Variable<PBoolean> DriveToTarget__timeout = new Variable<PBoolean>("DriveToTarget/timeout", BooleanValue.get((false)));
    private Variable<NodeFailureType> DriveToTarget__Drive__Drive__failure = new Variable<NodeFailureType>("DriveToTarget__Drive/Drive.failure", NodeFailureType.UNKNOWN);
    private SimpleCurrentNext<Integer> DriveToTarget__state = new SimpleCurrentNext<Integer>(0);
    private SimpleCurrentNext<Integer> DriveToTarget__Drive__state = new SimpleCurrentNext<Integer>(0);
    private SimpleCurrentNext<Integer> DriveToTarget__StopForTimeout__state = new SimpleCurrentNext<Integer>(0);
    private SimpleCurrentNext<Integer> DriveToTarget__StopForTimeout__Stop__state = new SimpleCurrentNext<Integer>(0);
    private SimpleCurrentNext<Integer> DriveToTarget__StopForTimeout__SetTimeoutFlag__state = new SimpleCurrentNext<Integer>(0);
    private SimpleCurrentNext<Integer> DriveToTarget__StopForTarget__state = new SimpleCurrentNext<Integer>(0);
    private SimpleCurrentNext<Integer> DriveToTarget__StopForTarget__Stop__state = new SimpleCurrentNext<Integer>(0);
    private SimpleCurrentNext<Integer> DriveToTarget__StopForTarget__SetDriveFlag__state = new SimpleCurrentNext<Integer>(0);
    private SimpleCurrentNext<Integer> DriveToTarget__TakeNavcam__state = new SimpleCurrentNext<Integer>(0);
    private SimpleCurrentNext<Integer> DriveToTarget__TakePancam__state = new SimpleCurrentNext<Integer>(0);

    void MicroStep___DriveToTarget() {
        PBoolean temp;
        switch (DriveToTarget__state.getCurrent()) {
            case  0 :
                if (getInterface().evalParentState().equalTo(NodeState.FINISHED).isTrue()) {
                    /*
(State #0) priority 1 ----> 
DriveToTarget : INACTIVE (1) -> FINISHED
<PARENT_FINISHED T?> (<root node's parent state> == FINISHED)
[ Set DriveToTarget.INACTIVE.END ]
[ Set DriveToTarget.FINISHED.START ]
[ Set outcome of DriveToTarget to SKIPPED ]
 ----> (State #6)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget : INACTIVE (1) -> FINISHED");
                    }
                    DriveToTarget__DriveToTarget__outcome.setValue(NodeOutcome.SKIPPED, 1);
                    commitAfterMicroStep(DriveToTarget__DriveToTarget__outcome);
                    DriveToTarget__state.setNext(6);
                    commitAfterMicroStep(DriveToTarget__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalParentState().equalTo(NodeState.EXECUTING).isTrue()) {
                        /*
(State #0) priority 1 ----> 
DriveToTarget : INACTIVE (1) -> WAITING
<PARENT_EXECUTING T?> (<root node's parent state> == EXECUTING)
[ Set DriveToTarget.INACTIVE.END ]
[ Set DriveToTarget.WAITING.START ]
 ----> (State #1)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget : INACTIVE (1) -> WAITING");
                        }
                        DriveToTarget__state.setNext(1);
                        commitAfterMicroStep(DriveToTarget__state);
                        changeOccurred();
                    }
                }
                break;
            case  1 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #1) priority 1 ----> 
DriveToTarget : WAITING (1) -> FINISHED
<ANCESTOR_EXITS_DISJOINED T?> (<root node's ancestor exit condition>)
[ Set DriveToTarget.WAITING.END ]
[ Set DriveToTarget.FINISHED.START ]
[ Set outcome of DriveToTarget to SKIPPED ]
 ----> (State #6)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget : WAITING (1) -> FINISHED");
                    }
                    DriveToTarget__DriveToTarget__outcome.setValue(NodeOutcome.SKIPPED, 1);
                    commitAfterMicroStep(DriveToTarget__DriveToTarget__outcome);
                    DriveToTarget__state.setNext(6);
                    commitAfterMicroStep(DriveToTarget__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #1) priority 3 ----> 
DriveToTarget : WAITING (3) -> FINISHED
<ANCESTOR_INVARIANTS_CONJOINED F?> (<root node's ancestor invariant condition>)
[ Set DriveToTarget.WAITING.END ]
[ Set DriveToTarget.FINISHED.START ]
[ Set outcome of DriveToTarget to SKIPPED ]
 ----> (State #6)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget : WAITING (3) -> FINISHED");
                        }
                        DriveToTarget__DriveToTarget__outcome.setValue(NodeOutcome.SKIPPED, 1);
                        commitAfterMicroStep(DriveToTarget__DriveToTarget__outcome);
                        DriveToTarget__state.setNext(6);
                        commitAfterMicroStep(DriveToTarget__state);
                        changeOccurred();
                    } else {
                        if (getInterface().evalAncestorEnd().isTrue()) {
                            /*
(State #1) priority 4 ----> 
DriveToTarget : WAITING (4) -> FINISHED
<ANCESTOR_ENDS_DISJOINED T?> (<root node's ancestor end condition>)
[ Set DriveToTarget.WAITING.END ]
[ Set DriveToTarget.FINISHED.START ]
[ Set outcome of DriveToTarget to SKIPPED ]
 ----> (State #6)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget : WAITING (4) -> FINISHED");
                            }
                            DriveToTarget__DriveToTarget__outcome.setValue(NodeOutcome.SKIPPED, 1);
                            commitAfterMicroStep(DriveToTarget__DriveToTarget__outcome);
                            DriveToTarget__state.setNext(6);
                            commitAfterMicroStep(DriveToTarget__state);
                            changeOccurred();
                        } else {
                            /*
(State #1) priority 6 ----> 
DriveToTarget : WAITING (6) -> EXECUTING
<START_CONDITION T?> (true)
<PRE_CONDITION T?> (true)
[ Set DriveToTarget.WAITING.END ]
[ Set DriveToTarget.EXECUTING.START ]
 ----> (State #2)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget : WAITING (6) -> EXECUTING");
                            }
                            DriveToTarget__state.setNext(2);
                            commitAfterMicroStep(DriveToTarget__state);
                            changeOccurred();
                        }
                    }
                }
                break;
            case  2 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #2) priority 1 ----> 
DriveToTarget : EXECUTING (1) -> FAILING
<ANCESTOR_EXITS_DISJOINED T?> (<root node's ancestor exit condition>)
[ Set DriveToTarget.EXECUTING.END ]
[ Set DriveToTarget.FAILING.START ]
[ Set outcome of DriveToTarget to INTERRUPTED, failure type PARENT_EXITED ]
 ----> (State #5)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget : EXECUTING (1) -> FAILING");
                    }
                    DriveToTarget__DriveToTarget__outcome.setValue(NodeOutcome.INTERRUPTED, 1);
                    commitAfterMicroStep(DriveToTarget__DriveToTarget__outcome);
                    DriveToTarget__DriveToTarget__failure.setValue(NodeFailureType.PARENT_EXITED, 1);
                    commitAfterMicroStep(DriveToTarget__DriveToTarget__failure);
                    DriveToTarget__state.setNext(5);
                    commitAfterMicroStep(DriveToTarget__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #2) priority 3 ----> 
DriveToTarget : EXECUTING (3) -> FAILING
<ANCESTOR_INVARIANTS_CONJOINED F?> (<root node's ancestor invariant condition>)
[ Set DriveToTarget.EXECUTING.END ]
[ Set DriveToTarget.FAILING.START ]
[ Set outcome of DriveToTarget to FAILURE, failure type PARENT_FAILED ]
 ----> (State #5)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget : EXECUTING (3) -> FAILING");
                        }
                        DriveToTarget__DriveToTarget__outcome.setValue(NodeOutcome.FAILURE, 1);
                        commitAfterMicroStep(DriveToTarget__DriveToTarget__outcome);
                        DriveToTarget__DriveToTarget__failure.setValue(NodeFailureType.PARENT_FAILED, 1);
                        commitAfterMicroStep(DriveToTarget__DriveToTarget__failure);
                        DriveToTarget__state.setNext(5);
                        commitAfterMicroStep(DriveToTarget__state);
                        changeOccurred();
                    } else {
                        if ((((NodeState.FINISHED.equalTo(STATE___DriveToTarget__Drive()).isTrue()&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTimeout()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTarget()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakeNavcam()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakePancam()).isTrue()) {
                            /*
(State #2) priority 5 ----> 
DriveToTarget : EXECUTING (5) -> FINISHING
<END_CONDITION T?> (FINISHED == DriveToTarget__Drive.state && FINISHED == DriveToTarget__StopForTimeout.state && FINISHED == DriveToTarget__StopForTarget.state && FINISHED == DriveToTarget__TakeNavcam.state && FINISHED == DriveToTarget__TakePancam.state)
[ Set DriveToTarget.EXECUTING.END ]
[ Set DriveToTarget.FINISHING.START ]
 ----> (State #3)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget : EXECUTING (5) -> FINISHING");
                            }
                            DriveToTarget__state.setNext(3);
                            commitAfterMicroStep(DriveToTarget__state);
                            changeOccurred();
                        }
                    }
                }
                break;
            case  3 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #3) priority 1 ----> 
DriveToTarget : FINISHING (1) -> FAILING
<ANCESTOR_EXITS_DISJOINED T?> (<root node's ancestor exit condition>)
[ Set DriveToTarget.FINISHING.END ]
[ Set DriveToTarget.FAILING.START ]
[ Set outcome of DriveToTarget to INTERRUPTED, failure type PARENT_EXITED ]
 ----> (State #5)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget : FINISHING (1) -> FAILING");
                    }
                    DriveToTarget__DriveToTarget__outcome.setValue(NodeOutcome.INTERRUPTED, 1);
                    commitAfterMicroStep(DriveToTarget__DriveToTarget__outcome);
                    DriveToTarget__DriveToTarget__failure.setValue(NodeFailureType.PARENT_EXITED, 1);
                    commitAfterMicroStep(DriveToTarget__DriveToTarget__failure);
                    DriveToTarget__state.setNext(5);
                    commitAfterMicroStep(DriveToTarget__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #3) priority 3 ----> 
DriveToTarget : FINISHING (3) -> FAILING
<ANCESTOR_INVARIANTS_CONJOINED F?> (<root node's ancestor invariant condition>)
[ Set DriveToTarget.FINISHING.END ]
[ Set DriveToTarget.FAILING.START ]
[ Set outcome of DriveToTarget to FAILURE, failure type PARENT_FAILED ]
 ----> (State #5)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget : FINISHING (3) -> FAILING");
                        }
                        DriveToTarget__DriveToTarget__outcome.setValue(NodeOutcome.FAILURE, 1);
                        commitAfterMicroStep(DriveToTarget__DriveToTarget__outcome);
                        DriveToTarget__DriveToTarget__failure.setValue(NodeFailureType.PARENT_FAILED, 1);
                        commitAfterMicroStep(DriveToTarget__DriveToTarget__failure);
                        DriveToTarget__state.setNext(5);
                        commitAfterMicroStep(DriveToTarget__state);
                        changeOccurred();
                    } else {
                        if (((((STATE___DriveToTarget__Drive().equalTo(NodeState.WAITING).isTrue()||STATE___DriveToTarget__Drive().equalTo(NodeState.FINISHED).isTrue())&&(STATE___DriveToTarget__StopForTimeout().equalTo(NodeState.WAITING).isTrue()||STATE___DriveToTarget__StopForTimeout().equalTo(NodeState.FINISHED).isTrue()))&&(STATE___DriveToTarget__StopForTarget().equalTo(NodeState.WAITING).isTrue()||STATE___DriveToTarget__StopForTarget().equalTo(NodeState.FINISHED).isTrue()))&&(STATE___DriveToTarget__TakeNavcam().equalTo(NodeState.WAITING).isTrue()||STATE___DriveToTarget__TakeNavcam().equalTo(NodeState.FINISHED).isTrue()))&&(STATE___DriveToTarget__TakePancam().equalTo(NodeState.WAITING).isTrue()||STATE___DriveToTarget__TakePancam().equalTo(NodeState.FINISHED).isTrue())) {
                            /*
(State #3) priority 5 ----> 
DriveToTarget : FINISHING (5) -> ITERATION_ENDED
<ALL_CHILDREN_WAITING_OR_FINISHED T?> (DriveToTarget__Drive.state == WAITING || DriveToTarget__Drive.state == FINISHED && DriveToTarget__StopForTimeout.state == WAITING || DriveToTarget__StopForTimeout.state == FINISHED && DriveToTarget__StopForTarget.state == WAITING || DriveToTarget__StopForTarget.state == FINISHED && DriveToTarget__TakeNavcam.state == WAITING || DriveToTarget__TakeNavcam.state == FINISHED && DriveToTarget__TakePancam.state == WAITING || DriveToTarget__TakePancam.state == FINISHED)
<POST_CONDITION T?> (true)
[ Set DriveToTarget.FINISHING.END ]
[ Set DriveToTarget.ITERATION_ENDED.START ]
[ Set outcome of DriveToTarget to SUCCESS ]
 ----> (State #4)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget : FINISHING (5) -> ITERATION_ENDED");
                            }
                            DriveToTarget__DriveToTarget__outcome.setValue(NodeOutcome.SUCCESS, 1);
                            commitAfterMicroStep(DriveToTarget__DriveToTarget__outcome);
                            DriveToTarget__state.setNext(4);
                            commitAfterMicroStep(DriveToTarget__state);
                            changeOccurred();
                        }
                    }
                }
                break;
            case  4 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #4) priority 1 ----> 
DriveToTarget : ITERATION_ENDED (1) -> FINISHED
<ANCESTOR_EXITS_DISJOINED T?> (<root node's ancestor exit condition>)
[ Set DriveToTarget.ITERATION_ENDED.END ]
[ Set DriveToTarget.FINISHED.START ]
[ Set outcome of DriveToTarget to INTERRUPTED, failure type PARENT_EXITED ]
 ----> (State #6)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget : ITERATION_ENDED (1) -> FINISHED");
                    }
                    DriveToTarget__DriveToTarget__outcome.setValue(NodeOutcome.INTERRUPTED, 1);
                    commitAfterMicroStep(DriveToTarget__DriveToTarget__outcome);
                    DriveToTarget__DriveToTarget__failure.setValue(NodeFailureType.PARENT_EXITED, 1);
                    commitAfterMicroStep(DriveToTarget__DriveToTarget__failure);
                    DriveToTarget__state.setNext(6);
                    commitAfterMicroStep(DriveToTarget__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #4) priority 2 ----> 
DriveToTarget : ITERATION_ENDED (2) -> FINISHED
<ANCESTOR_INVARIANTS_CONJOINED F?> (<root node's ancestor invariant condition>)
[ Set DriveToTarget.ITERATION_ENDED.END ]
[ Set DriveToTarget.FINISHED.START ]
[ Set outcome of DriveToTarget to FAILURE, failure type PARENT_FAILED ]
 ----> (State #6)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget : ITERATION_ENDED (2) -> FINISHED");
                        }
                        DriveToTarget__DriveToTarget__outcome.setValue(NodeOutcome.FAILURE, 1);
                        commitAfterMicroStep(DriveToTarget__DriveToTarget__outcome);
                        DriveToTarget__DriveToTarget__failure.setValue(NodeFailureType.PARENT_FAILED, 1);
                        commitAfterMicroStep(DriveToTarget__DriveToTarget__failure);
                        DriveToTarget__state.setNext(6);
                        commitAfterMicroStep(DriveToTarget__state);
                        changeOccurred();
                    } else {
                        if (getInterface().evalAncestorEnd().isTrue()) {
                            /*
(State #4) priority 3 ----> 
DriveToTarget : ITERATION_ENDED (3) -> FINISHED
<ANCESTOR_ENDS_DISJOINED T?> (<root node's ancestor end condition>)
[ Set DriveToTarget.ITERATION_ENDED.END ]
[ Set DriveToTarget.FINISHED.START ]
 ----> (State #6)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget : ITERATION_ENDED (3) -> FINISHED");
                            }
                            DriveToTarget__state.setNext(6);
                            commitAfterMicroStep(DriveToTarget__state);
                            changeOccurred();
                        } else {
                            /*
(State #4) priority 4 ----> 
DriveToTarget : ITERATION_ENDED (4) -> FINISHED
<REPEAT_CONDITION F?> (false)
[ Set DriveToTarget.ITERATION_ENDED.END ]
[ Set DriveToTarget.FINISHED.START ]
 ----> (State #6)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget : ITERATION_ENDED (4) -> FINISHED");
                            }
                            DriveToTarget__state.setNext(6);
                            commitAfterMicroStep(DriveToTarget__state);
                            changeOccurred();
                        }
                    }
                }
                break;
            case  6 :
                if (getInterface().evalParentState().equalTo(NodeState.WAITING).isTrue()) {
                    /*
(State #6) priority 1 ----> 
DriveToTarget : FINISHED (1) -> INACTIVE
<PARENT_WAITING T?> (<root node's parent state> == WAITING)
[ Set DriveToTarget.FINISHED.END ]
[ Set DriveToTarget.INACTIVE.START ]
[ Reset variables: DriveToTarget.EXECUTING.END, DriveToTarget.ITERATION_ENDED.START, DriveToTarget.outcome (DriveToTarget), DriveToTarget.INACTIVE.END, DriveToTarget.FAILING.END, drive_done (DriveToTarget), DriveToTarget.WAITING.START, DriveToTarget.EXECUTING.START, DriveToTarget.FAILING.START, DriveToTarget.INACTIVE.START, DriveToTarget.state, DriveToTarget.ITERATION_ENDED.END, DriveToTarget.FINISHING.END, DriveToTarget.FINISHED.END, DriveToTarget.failure (DriveToTarget), DriveToTarget.FINISHING.START, DriveToTarget.FINISHED.START, timeout (DriveToTarget), DriveToTarget.WAITING.END, ]
 ----> (State #0)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget : FINISHED (1) -> INACTIVE");
                    }
                    DriveToTarget__DriveToTarget__outcome.reset();
                    commitAfterMicroStep(DriveToTarget__DriveToTarget__outcome);
                    DriveToTarget__drive_done.reset();
                    commitAfterMicroStep(DriveToTarget__drive_done);
                    DriveToTarget__DriveToTarget__failure.reset();
                    commitAfterMicroStep(DriveToTarget__DriveToTarget__failure);
                    DriveToTarget__timeout.reset();
                    commitAfterMicroStep(DriveToTarget__timeout);
                    DriveToTarget__state.setNext(0);
                    commitAfterMicroStep(DriveToTarget__state);
                    changeOccurred();
                }
                break;
        }
        /* In Actions executed here: */
        switch (DriveToTarget__state.getNext()) {
            case  1 :
                MicroStep___DriveToTarget__StopForTarget();
                MicroStep___DriveToTarget__TakePancam();
                MicroStep___DriveToTarget__TakeNavcam();
                MicroStep___DriveToTarget__StopForTimeout();
                MicroStep___DriveToTarget__Drive();
                break;
            case  2 :
                MicroStep___DriveToTarget__StopForTarget();
                MicroStep___DriveToTarget__TakePancam();
                MicroStep___DriveToTarget__TakeNavcam();
                MicroStep___DriveToTarget__StopForTimeout();
                MicroStep___DriveToTarget__Drive();
                break;
            case  3 :
                MicroStep___DriveToTarget__StopForTarget();
                MicroStep___DriveToTarget__TakePancam();
                MicroStep___DriveToTarget__TakeNavcam();
                MicroStep___DriveToTarget__StopForTimeout();
                MicroStep___DriveToTarget__Drive();
                break;
            case  4 :
                MicroStep___DriveToTarget__StopForTarget();
                MicroStep___DriveToTarget__TakePancam();
                MicroStep___DriveToTarget__TakeNavcam();
                MicroStep___DriveToTarget__StopForTimeout();
                MicroStep___DriveToTarget__Drive();
                break;
            case  5 :
                MicroStep___DriveToTarget__StopForTarget();
                MicroStep___DriveToTarget__TakePancam();
                MicroStep___DriveToTarget__TakeNavcam();
                MicroStep___DriveToTarget__StopForTimeout();
                MicroStep___DriveToTarget__Drive();
                break;
            case  6 :
                MicroStep___DriveToTarget__StopForTarget();
                MicroStep___DriveToTarget__TakePancam();
                MicroStep___DriveToTarget__TakeNavcam();
                MicroStep___DriveToTarget__StopForTimeout();
                MicroStep___DriveToTarget__Drive();
                break;
        }
    }

    public NodeState STATE___DriveToTarget() {
        switch (DriveToTarget__state.getCurrent()) {
            case  3 :
                return NodeState.FINISHING;
            case  4 :
                return NodeState.ITERATION_ENDED;
            case  2 :
                return NodeState.EXECUTING;
            case  5 :
                return NodeState.FAILING;
            case  1 :
                return NodeState.WAITING;
            case  6 :
                return NodeState.FINISHED;
            case  0 :
                return NodeState.INACTIVE;
        }
        throw new RuntimeException("No state mapping found for DriveToTarget");
    }

    void MicroStep___DriveToTarget__Drive() {
        PBoolean temp;
        switch (DriveToTarget__Drive__state.getCurrent()) {
            case  0 :
                if (STATE___DriveToTarget().equalTo(NodeState.FINISHED).isTrue()) {
                    /*
(State #0) priority 1 ----> 
DriveToTarget__Drive : INACTIVE (1) -> FINISHED
<PARENT_FINISHED T?> (DriveToTarget.state == FINISHED)
[ Set DriveToTarget__Drive.INACTIVE.END ]
[ Set DriveToTarget__Drive.FINISHED.START ]
[ Set outcome of Drive to SKIPPED ]
 ----> (State #6)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__Drive : INACTIVE (1) -> FINISHED");
                    }
                    DriveToTarget__Drive__Drive__outcome.setValue(NodeOutcome.SKIPPED, 1);
                    commitAfterMicroStep(DriveToTarget__Drive__Drive__outcome);
                    DriveToTarget__Drive__state.setNext(6);
                    commitAfterMicroStep(DriveToTarget__Drive__state);
                    changeOccurred();
                } else {
                    if (STATE___DriveToTarget().equalTo(NodeState.EXECUTING).isTrue()) {
                        /*
(State #0) priority 1 ----> 
DriveToTarget__Drive : INACTIVE (1) -> WAITING
<PARENT_EXECUTING T?> (DriveToTarget.state == EXECUTING)
[ Set DriveToTarget__Drive.INACTIVE.END ]
[ Set DriveToTarget__Drive.WAITING.START ]
 ----> (State #1)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__Drive : INACTIVE (1) -> WAITING");
                        }
                        DriveToTarget__Drive__state.setNext(1);
                        commitAfterMicroStep(DriveToTarget__Drive__state);
                        changeOccurred();
                    }
                }
                break;
            case  1 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #1) priority 1 ----> 
DriveToTarget__Drive : WAITING (1) -> FINISHED
<ANCESTOR_EXITS_DISJOINED T?> (false || <root node's ancestor exit condition>)
[ Set DriveToTarget__Drive.WAITING.END ]
[ Set DriveToTarget__Drive.FINISHED.START ]
[ Set outcome of Drive to SKIPPED ]
 ----> (State #6)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__Drive : WAITING (1) -> FINISHED");
                    }
                    DriveToTarget__Drive__Drive__outcome.setValue(NodeOutcome.SKIPPED, 1);
                    commitAfterMicroStep(DriveToTarget__Drive__Drive__outcome);
                    DriveToTarget__Drive__state.setNext(6);
                    commitAfterMicroStep(DriveToTarget__Drive__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #1) priority 3 ----> 
DriveToTarget__Drive : WAITING (3) -> FINISHED
<ANCESTOR_INVARIANTS_CONJOINED F?> (true && true && <root node's ancestor invariant condition>)
[ Set DriveToTarget__Drive.WAITING.END ]
[ Set DriveToTarget__Drive.FINISHED.START ]
[ Set outcome of Drive to SKIPPED ]
 ----> (State #6)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__Drive : WAITING (3) -> FINISHED");
                        }
                        DriveToTarget__Drive__Drive__outcome.setValue(NodeOutcome.SKIPPED, 1);
                        commitAfterMicroStep(DriveToTarget__Drive__Drive__outcome);
                        DriveToTarget__Drive__state.setNext(6);
                        commitAfterMicroStep(DriveToTarget__Drive__state);
                        changeOccurred();
                    } else {
                        if (((((NodeState.FINISHED.equalTo(STATE___DriveToTarget__Drive()).isTrue()&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTimeout()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTarget()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakeNavcam()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakePancam()).isTrue())||getInterface().evalAncestorEnd().isTrue()) {
                            /*
(State #1) priority 4 ----> 
DriveToTarget__Drive : WAITING (4) -> FINISHED
<ANCESTOR_ENDS_DISJOINED T?> (FINISHED == DriveToTarget__Drive.state && FINISHED == DriveToTarget__StopForTimeout.state && FINISHED == DriveToTarget__StopForTarget.state && FINISHED == DriveToTarget__TakeNavcam.state && FINISHED == DriveToTarget__TakePancam.state || <root node's ancestor end condition>)
[ Set DriveToTarget__Drive.WAITING.END ]
[ Set DriveToTarget__Drive.FINISHED.START ]
[ Set outcome of Drive to SKIPPED ]
 ----> (State #6)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__Drive : WAITING (4) -> FINISHED");
                            }
                            DriveToTarget__Drive__Drive__outcome.setValue(NodeOutcome.SKIPPED, 1);
                            commitAfterMicroStep(DriveToTarget__Drive__Drive__outcome);
                            DriveToTarget__Drive__state.setNext(6);
                            commitAfterMicroStep(DriveToTarget__Drive__state);
                            changeOccurred();
                        } else {
                            /*
(State #1) priority 6 ----> 
DriveToTarget__Drive : WAITING (6) -> EXECUTING
<START_CONDITION T?> (true)
<PRE_CONDITION T?> (true)
[ Set DriveToTarget__Drive.WAITING.END ]
[ Set DriveToTarget__Drive.EXECUTING.START ]
 ----> (State #2)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__Drive : WAITING (6) -> EXECUTING");
                            }
                            getWorld().command(DriveToTarget__Drive__command_handle, StringValue.get(("rover_drive")), IntegerValue.get((10)));
                            endMacroStep();
                            DriveToTarget__Drive__state.setNext(2);
                            commitAfterMicroStep(DriveToTarget__Drive__state);
                            changeOccurred();
                        }
                    }
                }
                break;
            case  2 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #2) priority 1 ----> 
DriveToTarget__Drive : EXECUTING (1) -> FAILING
<ANCESTOR_EXITS_DISJOINED T?> (false || <root node's ancestor exit condition>)
[ Set DriveToTarget__Drive.EXECUTING.END ]
[ Set DriveToTarget__Drive.FAILING.START ]
[ Set outcome of Drive to INTERRUPTED, failure type PARENT_EXITED ]
 ----> (State #5)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__Drive : EXECUTING (1) -> FAILING");
                    }
                    DriveToTarget__Drive__Drive__outcome.setValue(NodeOutcome.INTERRUPTED, 1);
                    commitAfterMicroStep(DriveToTarget__Drive__Drive__outcome);
                    DriveToTarget__Drive__Drive__failure.setValue(NodeFailureType.PARENT_EXITED, 1);
                    commitAfterMicroStep(DriveToTarget__Drive__Drive__failure);
                    DriveToTarget__Drive__state.setNext(5);
                    commitAfterMicroStep(DriveToTarget__Drive__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #2) priority 3 ----> 
DriveToTarget__Drive : EXECUTING (3) -> FAILING
<ANCESTOR_INVARIANTS_CONJOINED F?> (true && true && <root node's ancestor invariant condition>)
[ Set DriveToTarget__Drive.EXECUTING.END ]
[ Set DriveToTarget__Drive.FAILING.START ]
[ Set outcome of Drive to FAILURE, failure type PARENT_FAILED ]
 ----> (State #5)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__Drive : EXECUTING (3) -> FAILING");
                        }
                        DriveToTarget__Drive__Drive__outcome.setValue(NodeOutcome.FAILURE, 1);
                        commitAfterMicroStep(DriveToTarget__Drive__Drive__outcome);
                        DriveToTarget__Drive__Drive__failure.setValue(NodeFailureType.PARENT_FAILED, 1);
                        commitAfterMicroStep(DriveToTarget__Drive__Drive__failure);
                        DriveToTarget__Drive__state.setNext(5);
                        commitAfterMicroStep(DriveToTarget__Drive__state);
                        changeOccurred();
                    } else {
                        if (BooleanValue.get(DriveToTarget__Drive__command_handle.getCommandHandle().isKnown()).isTrue()) {
                            /*
(State #2) priority 5 ----> 
DriveToTarget__Drive : EXECUTING (5) -> FINISHING
<END_CONDITION T?> (isKnown(DriveToTarget__Drive.command_handle))
[ Set DriveToTarget__Drive.EXECUTING.END ]
[ Set DriveToTarget__Drive.FINISHING.START ]
 ----> (State #3)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__Drive : EXECUTING (5) -> FINISHING");
                            }
                            DriveToTarget__Drive__state.setNext(3);
                            commitAfterMicroStep(DriveToTarget__Drive__state);
                            changeOccurred();
                        }
                    }
                }
                break;
            case  3 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #3) priority 1 ----> 
DriveToTarget__Drive : FINISHING (1) -> FAILING
<ANCESTOR_EXITS_DISJOINED T?> (false || <root node's ancestor exit condition>)
[ Set DriveToTarget__Drive.FINISHING.END ]
[ Set DriveToTarget__Drive.FAILING.START ]
[ Set outcome of Drive to INTERRUPTED, failure type PARENT_EXITED ]
 ----> (State #5)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__Drive : FINISHING (1) -> FAILING");
                    }
                    DriveToTarget__Drive__Drive__outcome.setValue(NodeOutcome.INTERRUPTED, 1);
                    commitAfterMicroStep(DriveToTarget__Drive__Drive__outcome);
                    DriveToTarget__Drive__Drive__failure.setValue(NodeFailureType.PARENT_EXITED, 1);
                    commitAfterMicroStep(DriveToTarget__Drive__Drive__failure);
                    DriveToTarget__Drive__state.setNext(5);
                    commitAfterMicroStep(DriveToTarget__Drive__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #3) priority 3 ----> 
DriveToTarget__Drive : FINISHING (3) -> FAILING
<ANCESTOR_INVARIANTS_CONJOINED F?> (true && true && <root node's ancestor invariant condition>)
[ Set DriveToTarget__Drive.FINISHING.END ]
[ Set DriveToTarget__Drive.FAILING.START ]
[ Set outcome of Drive to FAILURE, failure type PARENT_FAILED ]
 ----> (State #5)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__Drive : FINISHING (3) -> FAILING");
                        }
                        DriveToTarget__Drive__Drive__outcome.setValue(NodeOutcome.FAILURE, 1);
                        commitAfterMicroStep(DriveToTarget__Drive__Drive__outcome);
                        DriveToTarget__Drive__Drive__failure.setValue(NodeFailureType.PARENT_FAILED, 1);
                        commitAfterMicroStep(DriveToTarget__Drive__Drive__failure);
                        DriveToTarget__Drive__state.setNext(5);
                        commitAfterMicroStep(DriveToTarget__Drive__state);
                        changeOccurred();
                    } else {
                        if (BooleanValue.get(DriveToTarget__Drive__command_handle.getCommandHandle().isKnown()).isTrue()) {
                            /*
(State #3) priority 5 ----> 
DriveToTarget__Drive : FINISHING (5) -> ITERATION_ENDED
<COMMAND_ACCEPTED T?> (isKnown(DriveToTarget__Drive.command_handle))
<POST_CONDITION T?> (true)
[ Set DriveToTarget__Drive.FINISHING.END ]
[ Set DriveToTarget__Drive.ITERATION_ENDED.START ]
[ Set outcome of Drive to SUCCESS ]
 ----> (State #4)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__Drive : FINISHING (5) -> ITERATION_ENDED");
                            }
                            DriveToTarget__Drive__Drive__outcome.setValue(NodeOutcome.SUCCESS, 1);
                            commitAfterMicroStep(DriveToTarget__Drive__Drive__outcome);
                            DriveToTarget__Drive__state.setNext(4);
                            commitAfterMicroStep(DriveToTarget__Drive__state);
                            changeOccurred();
                        }
                    }
                }
                break;
            case  4 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #4) priority 1 ----> 
DriveToTarget__Drive : ITERATION_ENDED (1) -> FINISHED
<ANCESTOR_EXITS_DISJOINED T?> (false || <root node's ancestor exit condition>)
[ Set DriveToTarget__Drive.ITERATION_ENDED.END ]
[ Set DriveToTarget__Drive.FINISHED.START ]
[ Set outcome of Drive to INTERRUPTED, failure type PARENT_EXITED ]
 ----> (State #6)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__Drive : ITERATION_ENDED (1) -> FINISHED");
                    }
                    DriveToTarget__Drive__Drive__outcome.setValue(NodeOutcome.INTERRUPTED, 1);
                    commitAfterMicroStep(DriveToTarget__Drive__Drive__outcome);
                    DriveToTarget__Drive__Drive__failure.setValue(NodeFailureType.PARENT_EXITED, 1);
                    commitAfterMicroStep(DriveToTarget__Drive__Drive__failure);
                    DriveToTarget__Drive__state.setNext(6);
                    commitAfterMicroStep(DriveToTarget__Drive__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #4) priority 2 ----> 
DriveToTarget__Drive : ITERATION_ENDED (2) -> FINISHED
<ANCESTOR_INVARIANTS_CONJOINED F?> (true && true && <root node's ancestor invariant condition>)
[ Set DriveToTarget__Drive.ITERATION_ENDED.END ]
[ Set DriveToTarget__Drive.FINISHED.START ]
[ Set outcome of Drive to FAILURE, failure type PARENT_FAILED ]
 ----> (State #6)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__Drive : ITERATION_ENDED (2) -> FINISHED");
                        }
                        DriveToTarget__Drive__Drive__outcome.setValue(NodeOutcome.FAILURE, 1);
                        commitAfterMicroStep(DriveToTarget__Drive__Drive__outcome);
                        DriveToTarget__Drive__Drive__failure.setValue(NodeFailureType.PARENT_FAILED, 1);
                        commitAfterMicroStep(DriveToTarget__Drive__Drive__failure);
                        DriveToTarget__Drive__state.setNext(6);
                        commitAfterMicroStep(DriveToTarget__Drive__state);
                        changeOccurred();
                    } else {
                        if (((((NodeState.FINISHED.equalTo(STATE___DriveToTarget__Drive()).isTrue()&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTimeout()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTarget()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakeNavcam()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakePancam()).isTrue())||getInterface().evalAncestorEnd().isTrue()) {
                            /*
(State #4) priority 3 ----> 
DriveToTarget__Drive : ITERATION_ENDED (3) -> FINISHED
<ANCESTOR_ENDS_DISJOINED T?> (FINISHED == DriveToTarget__Drive.state && FINISHED == DriveToTarget__StopForTimeout.state && FINISHED == DriveToTarget__StopForTarget.state && FINISHED == DriveToTarget__TakeNavcam.state && FINISHED == DriveToTarget__TakePancam.state || <root node's ancestor end condition>)
[ Set DriveToTarget__Drive.ITERATION_ENDED.END ]
[ Set DriveToTarget__Drive.FINISHED.START ]
 ----> (State #6)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__Drive : ITERATION_ENDED (3) -> FINISHED");
                            }
                            DriveToTarget__Drive__state.setNext(6);
                            commitAfterMicroStep(DriveToTarget__Drive__state);
                            changeOccurred();
                        } else {
                            /*
(State #4) priority 4 ----> 
DriveToTarget__Drive : ITERATION_ENDED (4) -> FINISHED
<REPEAT_CONDITION F?> (false)
[ Set DriveToTarget__Drive.ITERATION_ENDED.END ]
[ Set DriveToTarget__Drive.FINISHED.START ]
 ----> (State #6)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__Drive : ITERATION_ENDED (4) -> FINISHED");
                            }
                            DriveToTarget__Drive__state.setNext(6);
                            commitAfterMicroStep(DriveToTarget__Drive__state);
                            changeOccurred();
                        }
                    }
                }
                break;
            case  6 :
                if (STATE___DriveToTarget().equalTo(NodeState.WAITING).isTrue()) {
                    /*
(State #6) priority 1 ----> 
DriveToTarget__Drive : FINISHED (1) -> INACTIVE
<PARENT_WAITING T?> (DriveToTarget.state == WAITING)
[ Set DriveToTarget__Drive.FINISHED.END ]
[ Set DriveToTarget__Drive.INACTIVE.START ]
[ Reset variables: DriveToTarget__Drive.EXECUTING.END, DriveToTarget__Drive.ITERATION_ENDED.START, Drive.outcome (DriveToTarget__Drive), DriveToTarget__Drive.INACTIVE.END, DriveToTarget__Drive.FAILING.END, DriveToTarget__Drive.WAITING.START, DriveToTarget__Drive.EXECUTING.START, DriveToTarget__Drive.command_handle, DriveToTarget__Drive.FAILING.START, DriveToTarget__Drive.INACTIVE.START, DriveToTarget__Drive.state, DriveToTarget__Drive.ITERATION_ENDED.END, DriveToTarget__Drive.FINISHING.END, DriveToTarget__Drive.FINISHED.END, Drive.failure (DriveToTarget__Drive), DriveToTarget__Drive.FINISHING.START, DriveToTarget__Drive.FINISHED.START, DriveToTarget__Drive.WAITING.END, ]
 ----> (State #0)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__Drive : FINISHED (1) -> INACTIVE");
                    }
                    DriveToTarget__Drive__Drive__outcome.reset();
                    commitAfterMicroStep(DriveToTarget__Drive__Drive__outcome);
                    DriveToTarget__Drive__command_handle.reset();
                    DriveToTarget__Drive__Drive__failure.reset();
                    commitAfterMicroStep(DriveToTarget__Drive__Drive__failure);
                    DriveToTarget__Drive__state.setNext(0);
                    commitAfterMicroStep(DriveToTarget__Drive__state);
                    changeOccurred();
                }
                break;
        }
        /* In Actions executed here: */
        switch (DriveToTarget__Drive__state.getNext()) {
        }
    }

    public NodeState STATE___DriveToTarget__Drive() {
        switch (DriveToTarget__Drive__state.getCurrent()) {
            case  3 :
                return NodeState.FINISHING;
            case  4 :
                return NodeState.ITERATION_ENDED;
            case  2 :
                return NodeState.EXECUTING;
            case  5 :
                return NodeState.FAILING;
            case  1 :
                return NodeState.WAITING;
            case  6 :
                return NodeState.FINISHED;
            case  0 :
                return NodeState.INACTIVE;
        }
        throw new RuntimeException("No state mapping found for DriveToTarget__Drive");
    }

    void MicroStep___DriveToTarget__StopForTimeout() {
        PBoolean temp;
        switch (DriveToTarget__StopForTimeout__state.getCurrent()) {
            case  0 :
                if (STATE___DriveToTarget().equalTo(NodeState.FINISHED).isTrue()) {
                    /*
(State #0) priority 1 ----> 
DriveToTarget__StopForTimeout : INACTIVE (1) -> FINISHED
<PARENT_FINISHED T?> (DriveToTarget.state == FINISHED)
[ Set DriveToTarget__StopForTimeout.INACTIVE.END ]
[ Set DriveToTarget__StopForTimeout.FINISHED.START ]
[ Set outcome of StopForTimeout to SKIPPED ]
 ----> (State #6)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__StopForTimeout : INACTIVE (1) -> FINISHED");
                    }
                    DriveToTarget__StopForTimeout__StopForTimeout__outcome.setValue(NodeOutcome.SKIPPED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__StopForTimeout__outcome);
                    DriveToTarget__StopForTimeout__state.setNext(6);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__state);
                    changeOccurred();
                } else {
                    if (STATE___DriveToTarget().equalTo(NodeState.EXECUTING).isTrue()) {
                        /*
(State #0) priority 1 ----> 
DriveToTarget__StopForTimeout : INACTIVE (1) -> WAITING
<PARENT_EXECUTING T?> (DriveToTarget.state == EXECUTING)
[ Set DriveToTarget__StopForTimeout.INACTIVE.END ]
[ Set DriveToTarget__StopForTimeout.WAITING.START ]
 ----> (State #1)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__StopForTimeout : INACTIVE (1) -> WAITING");
                        }
                        DriveToTarget__StopForTimeout__state.setNext(1);
                        commitAfterMicroStep(DriveToTarget__StopForTimeout__state);
                        changeOccurred();
                    }
                }
                break;
            case  1 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #1) priority 1 ----> 
DriveToTarget__StopForTimeout : WAITING (1) -> FINISHED
<ANCESTOR_EXITS_DISJOINED T?> (false || <root node's ancestor exit condition>)
[ Set DriveToTarget__StopForTimeout.WAITING.END ]
[ Set DriveToTarget__StopForTimeout.FINISHED.START ]
[ Set outcome of StopForTimeout to SKIPPED ]
 ----> (State #6)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__StopForTimeout : WAITING (1) -> FINISHED");
                    }
                    DriveToTarget__StopForTimeout__StopForTimeout__outcome.setValue(NodeOutcome.SKIPPED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__StopForTimeout__outcome);
                    DriveToTarget__StopForTimeout__state.setNext(6);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #1) priority 3 ----> 
DriveToTarget__StopForTimeout : WAITING (3) -> FINISHED
<ANCESTOR_INVARIANTS_CONJOINED F?> (true && true && <root node's ancestor invariant condition>)
[ Set DriveToTarget__StopForTimeout.WAITING.END ]
[ Set DriveToTarget__StopForTimeout.FINISHED.START ]
[ Set outcome of StopForTimeout to SKIPPED ]
 ----> (State #6)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__StopForTimeout : WAITING (3) -> FINISHED");
                        }
                        DriveToTarget__StopForTimeout__StopForTimeout__outcome.setValue(NodeOutcome.SKIPPED, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTimeout__StopForTimeout__outcome);
                        DriveToTarget__StopForTimeout__state.setNext(6);
                        commitAfterMicroStep(DriveToTarget__StopForTimeout__state);
                        changeOccurred();
                    } else {
                        if (((((NodeState.FINISHED.equalTo(STATE___DriveToTarget__Drive()).isTrue()&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTimeout()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTarget()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakeNavcam()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakePancam()).isTrue())||getInterface().evalAncestorEnd().isTrue()) {
                            /*
(State #1) priority 4 ----> 
DriveToTarget__StopForTimeout : WAITING (4) -> FINISHED
<ANCESTOR_ENDS_DISJOINED T?> (FINISHED == DriveToTarget__Drive.state && FINISHED == DriveToTarget__StopForTimeout.state && FINISHED == DriveToTarget__StopForTarget.state && FINISHED == DriveToTarget__TakeNavcam.state && FINISHED == DriveToTarget__TakePancam.state || <root node's ancestor end condition>)
[ Set DriveToTarget__StopForTimeout.WAITING.END ]
[ Set DriveToTarget__StopForTimeout.FINISHED.START ]
[ Set outcome of StopForTimeout to SKIPPED ]
 ----> (State #6)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__StopForTimeout : WAITING (4) -> FINISHED");
                            }
                            DriveToTarget__StopForTimeout__StopForTimeout__outcome.setValue(NodeOutcome.SKIPPED, 1);
                            commitAfterMicroStep(DriveToTarget__StopForTimeout__StopForTimeout__outcome);
                            DriveToTarget__StopForTimeout__state.setNext(6);
                            commitAfterMicroStep(DriveToTarget__StopForTimeout__state);
                            changeOccurred();
                        } else {
                            if (((PNumeric) getWorld().lookupOnChange(StringValue.get(("time")), RealValue.get((0.1)))).ge(IntegerValue.get((10))).isTrue()) {
                                /*
(State #1) priority 6 ----> 
DriveToTarget__StopForTimeout : WAITING (6) -> EXECUTING
<START_CONDITION T?> ((PNumeric) (LookupOnChange("time", 0.1)) >= 10)
<PRE_CONDITION T?> (true)
[ Set DriveToTarget__StopForTimeout.WAITING.END ]
[ Set DriveToTarget__StopForTimeout.EXECUTING.START ]
 ----> (State #2)
*/
                                if (JavaPlan.DEBUG) {
                                    System.out.println("DriveToTarget__StopForTimeout : WAITING (6) -> EXECUTING");
                                }
                                DriveToTarget__StopForTimeout__state.setNext(2);
                                commitAfterMicroStep(DriveToTarget__StopForTimeout__state);
                                changeOccurred();
                            }
                        }
                    }
                }
                break;
            case  2 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #2) priority 1 ----> 
DriveToTarget__StopForTimeout : EXECUTING (1) -> FAILING
<ANCESTOR_EXITS_DISJOINED T?> (false || <root node's ancestor exit condition>)
[ Set DriveToTarget__StopForTimeout.EXECUTING.END ]
[ Set DriveToTarget__StopForTimeout.FAILING.START ]
[ Set outcome of StopForTimeout to INTERRUPTED, failure type PARENT_EXITED ]
 ----> (State #5)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__StopForTimeout : EXECUTING (1) -> FAILING");
                    }
                    DriveToTarget__StopForTimeout__StopForTimeout__outcome.setValue(NodeOutcome.INTERRUPTED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__StopForTimeout__outcome);
                    DriveToTarget__StopForTimeout__StopForTimeout__failure.setValue(NodeFailureType.PARENT_EXITED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__StopForTimeout__failure);
                    DriveToTarget__StopForTimeout__state.setNext(5);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #2) priority 3 ----> 
DriveToTarget__StopForTimeout : EXECUTING (3) -> FAILING
<ANCESTOR_INVARIANTS_CONJOINED F?> (true && true && <root node's ancestor invariant condition>)
[ Set DriveToTarget__StopForTimeout.EXECUTING.END ]
[ Set DriveToTarget__StopForTimeout.FAILING.START ]
[ Set outcome of StopForTimeout to FAILURE, failure type PARENT_FAILED ]
 ----> (State #5)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__StopForTimeout : EXECUTING (3) -> FAILING");
                        }
                        DriveToTarget__StopForTimeout__StopForTimeout__outcome.setValue(NodeOutcome.FAILURE, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTimeout__StopForTimeout__outcome);
                        DriveToTarget__StopForTimeout__StopForTimeout__failure.setValue(NodeFailureType.PARENT_FAILED, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTimeout__StopForTimeout__failure);
                        DriveToTarget__StopForTimeout__state.setNext(5);
                        commitAfterMicroStep(DriveToTarget__StopForTimeout__state);
                        changeOccurred();
                    } else {
                        if (NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTimeout__Stop()).isTrue()&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTimeout__SetTimeoutFlag()).isTrue()) {
                            /*
(State #2) priority 5 ----> 
DriveToTarget__StopForTimeout : EXECUTING (5) -> FINISHING
<END_CONDITION T?> (FINISHED == DriveToTarget__StopForTimeout__Stop.state && FINISHED == DriveToTarget__StopForTimeout__SetTimeoutFlag.state)
[ Set DriveToTarget__StopForTimeout.EXECUTING.END ]
[ Set DriveToTarget__StopForTimeout.FINISHING.START ]
 ----> (State #3)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__StopForTimeout : EXECUTING (5) -> FINISHING");
                            }
                            DriveToTarget__StopForTimeout__state.setNext(3);
                            commitAfterMicroStep(DriveToTarget__StopForTimeout__state);
                            changeOccurred();
                        }
                    }
                }
                break;
            case  3 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #3) priority 1 ----> 
DriveToTarget__StopForTimeout : FINISHING (1) -> FAILING
<ANCESTOR_EXITS_DISJOINED T?> (false || <root node's ancestor exit condition>)
[ Set DriveToTarget__StopForTimeout.FINISHING.END ]
[ Set DriveToTarget__StopForTimeout.FAILING.START ]
[ Set outcome of StopForTimeout to INTERRUPTED, failure type PARENT_EXITED ]
 ----> (State #5)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__StopForTimeout : FINISHING (1) -> FAILING");
                    }
                    DriveToTarget__StopForTimeout__StopForTimeout__outcome.setValue(NodeOutcome.INTERRUPTED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__StopForTimeout__outcome);
                    DriveToTarget__StopForTimeout__StopForTimeout__failure.setValue(NodeFailureType.PARENT_EXITED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__StopForTimeout__failure);
                    DriveToTarget__StopForTimeout__state.setNext(5);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #3) priority 3 ----> 
DriveToTarget__StopForTimeout : FINISHING (3) -> FAILING
<ANCESTOR_INVARIANTS_CONJOINED F?> (true && true && <root node's ancestor invariant condition>)
[ Set DriveToTarget__StopForTimeout.FINISHING.END ]
[ Set DriveToTarget__StopForTimeout.FAILING.START ]
[ Set outcome of StopForTimeout to FAILURE, failure type PARENT_FAILED ]
 ----> (State #5)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__StopForTimeout : FINISHING (3) -> FAILING");
                        }
                        DriveToTarget__StopForTimeout__StopForTimeout__outcome.setValue(NodeOutcome.FAILURE, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTimeout__StopForTimeout__outcome);
                        DriveToTarget__StopForTimeout__StopForTimeout__failure.setValue(NodeFailureType.PARENT_FAILED, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTimeout__StopForTimeout__failure);
                        DriveToTarget__StopForTimeout__state.setNext(5);
                        commitAfterMicroStep(DriveToTarget__StopForTimeout__state);
                        changeOccurred();
                    } else {
                        if ((STATE___DriveToTarget__StopForTimeout__Stop().equalTo(NodeState.WAITING).isTrue()||STATE___DriveToTarget__StopForTimeout__Stop().equalTo(NodeState.FINISHED).isTrue())&&(STATE___DriveToTarget__StopForTimeout__SetTimeoutFlag().equalTo(NodeState.WAITING).isTrue()||STATE___DriveToTarget__StopForTimeout__SetTimeoutFlag().equalTo(NodeState.FINISHED).isTrue())) {
                            /*
(State #3) priority 5 ----> 
DriveToTarget__StopForTimeout : FINISHING (5) -> ITERATION_ENDED
<ALL_CHILDREN_WAITING_OR_FINISHED T?> (DriveToTarget__StopForTimeout__Stop.state == WAITING || DriveToTarget__StopForTimeout__Stop.state == FINISHED && DriveToTarget__StopForTimeout__SetTimeoutFlag.state == WAITING || DriveToTarget__StopForTimeout__SetTimeoutFlag.state == FINISHED)
<POST_CONDITION T?> (true)
[ Set DriveToTarget__StopForTimeout.FINISHING.END ]
[ Set DriveToTarget__StopForTimeout.ITERATION_ENDED.START ]
[ Set outcome of StopForTimeout to SUCCESS ]
 ----> (State #4)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__StopForTimeout : FINISHING (5) -> ITERATION_ENDED");
                            }
                            DriveToTarget__StopForTimeout__StopForTimeout__outcome.setValue(NodeOutcome.SUCCESS, 1);
                            commitAfterMicroStep(DriveToTarget__StopForTimeout__StopForTimeout__outcome);
                            DriveToTarget__StopForTimeout__state.setNext(4);
                            commitAfterMicroStep(DriveToTarget__StopForTimeout__state);
                            changeOccurred();
                        }
                    }
                }
                break;
            case  4 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #4) priority 1 ----> 
DriveToTarget__StopForTimeout : ITERATION_ENDED (1) -> FINISHED
<ANCESTOR_EXITS_DISJOINED T?> (false || <root node's ancestor exit condition>)
[ Set DriveToTarget__StopForTimeout.ITERATION_ENDED.END ]
[ Set DriveToTarget__StopForTimeout.FINISHED.START ]
[ Set outcome of StopForTimeout to INTERRUPTED, failure type PARENT_EXITED ]
 ----> (State #6)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__StopForTimeout : ITERATION_ENDED (1) -> FINISHED");
                    }
                    DriveToTarget__StopForTimeout__StopForTimeout__outcome.setValue(NodeOutcome.INTERRUPTED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__StopForTimeout__outcome);
                    DriveToTarget__StopForTimeout__StopForTimeout__failure.setValue(NodeFailureType.PARENT_EXITED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__StopForTimeout__failure);
                    DriveToTarget__StopForTimeout__state.setNext(6);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #4) priority 2 ----> 
DriveToTarget__StopForTimeout : ITERATION_ENDED (2) -> FINISHED
<ANCESTOR_INVARIANTS_CONJOINED F?> (true && true && <root node's ancestor invariant condition>)
[ Set DriveToTarget__StopForTimeout.ITERATION_ENDED.END ]
[ Set DriveToTarget__StopForTimeout.FINISHED.START ]
[ Set outcome of StopForTimeout to FAILURE, failure type PARENT_FAILED ]
 ----> (State #6)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__StopForTimeout : ITERATION_ENDED (2) -> FINISHED");
                        }
                        DriveToTarget__StopForTimeout__StopForTimeout__outcome.setValue(NodeOutcome.FAILURE, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTimeout__StopForTimeout__outcome);
                        DriveToTarget__StopForTimeout__StopForTimeout__failure.setValue(NodeFailureType.PARENT_FAILED, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTimeout__StopForTimeout__failure);
                        DriveToTarget__StopForTimeout__state.setNext(6);
                        commitAfterMicroStep(DriveToTarget__StopForTimeout__state);
                        changeOccurred();
                    } else {
                        if (((((NodeState.FINISHED.equalTo(STATE___DriveToTarget__Drive()).isTrue()&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTimeout()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTarget()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakeNavcam()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakePancam()).isTrue())||getInterface().evalAncestorEnd().isTrue()) {
                            /*
(State #4) priority 3 ----> 
DriveToTarget__StopForTimeout : ITERATION_ENDED (3) -> FINISHED
<ANCESTOR_ENDS_DISJOINED T?> (FINISHED == DriveToTarget__Drive.state && FINISHED == DriveToTarget__StopForTimeout.state && FINISHED == DriveToTarget__StopForTarget.state && FINISHED == DriveToTarget__TakeNavcam.state && FINISHED == DriveToTarget__TakePancam.state || <root node's ancestor end condition>)
[ Set DriveToTarget__StopForTimeout.ITERATION_ENDED.END ]
[ Set DriveToTarget__StopForTimeout.FINISHED.START ]
 ----> (State #6)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__StopForTimeout : ITERATION_ENDED (3) -> FINISHED");
                            }
                            DriveToTarget__StopForTimeout__state.setNext(6);
                            commitAfterMicroStep(DriveToTarget__StopForTimeout__state);
                            changeOccurred();
                        } else {
                            /*
(State #4) priority 4 ----> 
DriveToTarget__StopForTimeout : ITERATION_ENDED (4) -> FINISHED
<REPEAT_CONDITION F?> (false)
[ Set DriveToTarget__StopForTimeout.ITERATION_ENDED.END ]
[ Set DriveToTarget__StopForTimeout.FINISHED.START ]
 ----> (State #6)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__StopForTimeout : ITERATION_ENDED (4) -> FINISHED");
                            }
                            DriveToTarget__StopForTimeout__state.setNext(6);
                            commitAfterMicroStep(DriveToTarget__StopForTimeout__state);
                            changeOccurred();
                        }
                    }
                }
                break;
            case  6 :
                if (STATE___DriveToTarget().equalTo(NodeState.WAITING).isTrue()) {
                    /*
(State #6) priority 1 ----> 
DriveToTarget__StopForTimeout : FINISHED (1) -> INACTIVE
<PARENT_WAITING T?> (DriveToTarget.state == WAITING)
[ Set DriveToTarget__StopForTimeout.FINISHED.END ]
[ Set DriveToTarget__StopForTimeout.INACTIVE.START ]
[ Reset variables: DriveToTarget__StopForTimeout.EXECUTING.END, DriveToTarget__StopForTimeout.ITERATION_ENDED.START, StopForTimeout.outcome (DriveToTarget__StopForTimeout), DriveToTarget__StopForTimeout.INACTIVE.END, DriveToTarget__StopForTimeout.FAILING.END, DriveToTarget__StopForTimeout.WAITING.START, DriveToTarget__StopForTimeout.EXECUTING.START, DriveToTarget__StopForTimeout.FAILING.START, DriveToTarget__StopForTimeout.INACTIVE.START, DriveToTarget__StopForTimeout.state, DriveToTarget__StopForTimeout.ITERATION_ENDED.END, DriveToTarget__StopForTimeout.FINISHING.END, DriveToTarget__StopForTimeout.FINISHED.END, StopForTimeout.failure (DriveToTarget__StopForTimeout), DriveToTarget__StopForTimeout.FINISHING.START, DriveToTarget__StopForTimeout.FINISHED.START, DriveToTarget__StopForTimeout.WAITING.END, ]
 ----> (State #0)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__StopForTimeout : FINISHED (1) -> INACTIVE");
                    }
                    DriveToTarget__StopForTimeout__StopForTimeout__outcome.reset();
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__StopForTimeout__outcome);
                    DriveToTarget__StopForTimeout__StopForTimeout__failure.reset();
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__StopForTimeout__failure);
                    DriveToTarget__StopForTimeout__state.setNext(0);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__state);
                    changeOccurred();
                }
                break;
        }
        /* In Actions executed here: */
        switch (DriveToTarget__StopForTimeout__state.getNext()) {
            case  1 :
                MicroStep___DriveToTarget__StopForTimeout__Stop();
                MicroStep___DriveToTarget__StopForTimeout__SetTimeoutFlag();
                break;
            case  2 :
                MicroStep___DriveToTarget__StopForTimeout__Stop();
                MicroStep___DriveToTarget__StopForTimeout__SetTimeoutFlag();
                break;
            case  3 :
                MicroStep___DriveToTarget__StopForTimeout__Stop();
                MicroStep___DriveToTarget__StopForTimeout__SetTimeoutFlag();
                break;
            case  4 :
                MicroStep___DriveToTarget__StopForTimeout__Stop();
                MicroStep___DriveToTarget__StopForTimeout__SetTimeoutFlag();
                break;
            case  5 :
                MicroStep___DriveToTarget__StopForTimeout__Stop();
                MicroStep___DriveToTarget__StopForTimeout__SetTimeoutFlag();
                break;
            case  6 :
                MicroStep___DriveToTarget__StopForTimeout__Stop();
                MicroStep___DriveToTarget__StopForTimeout__SetTimeoutFlag();
                break;
        }
    }

    public NodeState STATE___DriveToTarget__StopForTimeout() {
        switch (DriveToTarget__StopForTimeout__state.getCurrent()) {
            case  3 :
                return NodeState.FINISHING;
            case  4 :
                return NodeState.ITERATION_ENDED;
            case  2 :
                return NodeState.EXECUTING;
            case  5 :
                return NodeState.FAILING;
            case  1 :
                return NodeState.WAITING;
            case  6 :
                return NodeState.FINISHED;
            case  0 :
                return NodeState.INACTIVE;
        }
        throw new RuntimeException("No state mapping found for DriveToTarget__StopForTimeout");
    }

    void MicroStep___DriveToTarget__StopForTimeout__Stop() {
        PBoolean temp;
        switch (DriveToTarget__StopForTimeout__Stop__state.getCurrent()) {
            case  0 :
                if (STATE___DriveToTarget__StopForTimeout().equalTo(NodeState.FINISHED).isTrue()) {
                    /*
(State #0) priority 1 ----> 
DriveToTarget__StopForTimeout__Stop : INACTIVE (1) -> FINISHED
<PARENT_FINISHED T?> (DriveToTarget__StopForTimeout.state == FINISHED)
[ Set DriveToTarget__StopForTimeout__Stop.INACTIVE.END ]
[ Set DriveToTarget__StopForTimeout__Stop.FINISHED.START ]
[ Set outcome of Stop to SKIPPED ]
 ----> (State #6)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__StopForTimeout__Stop : INACTIVE (1) -> FINISHED");
                    }
                    DriveToTarget__StopForTimeout__Stop__Stop__outcome.setValue(NodeOutcome.SKIPPED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__Stop__Stop__outcome);
                    DriveToTarget__StopForTimeout__Stop__state.setNext(6);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__Stop__state);
                    changeOccurred();
                } else {
                    if (STATE___DriveToTarget__StopForTimeout().equalTo(NodeState.EXECUTING).isTrue()) {
                        /*
(State #0) priority 1 ----> 
DriveToTarget__StopForTimeout__Stop : INACTIVE (1) -> WAITING
<PARENT_EXECUTING T?> (DriveToTarget__StopForTimeout.state == EXECUTING)
[ Set DriveToTarget__StopForTimeout__Stop.INACTIVE.END ]
[ Set DriveToTarget__StopForTimeout__Stop.WAITING.START ]
 ----> (State #1)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__StopForTimeout__Stop : INACTIVE (1) -> WAITING");
                        }
                        DriveToTarget__StopForTimeout__Stop__state.setNext(1);
                        commitAfterMicroStep(DriveToTarget__StopForTimeout__Stop__state);
                        changeOccurred();
                    }
                }
                break;
            case  1 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #1) priority 1 ----> 
DriveToTarget__StopForTimeout__Stop : WAITING (1) -> FINISHED
<ANCESTOR_EXITS_DISJOINED T?> (false || false || <root node's ancestor exit condition>)
[ Set DriveToTarget__StopForTimeout__Stop.WAITING.END ]
[ Set DriveToTarget__StopForTimeout__Stop.FINISHED.START ]
[ Set outcome of Stop to SKIPPED ]
 ----> (State #6)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__StopForTimeout__Stop : WAITING (1) -> FINISHED");
                    }
                    DriveToTarget__StopForTimeout__Stop__Stop__outcome.setValue(NodeOutcome.SKIPPED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__Stop__Stop__outcome);
                    DriveToTarget__StopForTimeout__Stop__state.setNext(6);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__Stop__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #1) priority 3 ----> 
DriveToTarget__StopForTimeout__Stop : WAITING (3) -> FINISHED
<ANCESTOR_INVARIANTS_CONJOINED F?> (true && true && true && <root node's ancestor invariant condition>)
[ Set DriveToTarget__StopForTimeout__Stop.WAITING.END ]
[ Set DriveToTarget__StopForTimeout__Stop.FINISHED.START ]
[ Set outcome of Stop to SKIPPED ]
 ----> (State #6)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__StopForTimeout__Stop : WAITING (3) -> FINISHED");
                        }
                        DriveToTarget__StopForTimeout__Stop__Stop__outcome.setValue(NodeOutcome.SKIPPED, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTimeout__Stop__Stop__outcome);
                        DriveToTarget__StopForTimeout__Stop__state.setNext(6);
                        commitAfterMicroStep(DriveToTarget__StopForTimeout__Stop__state);
                        changeOccurred();
                    } else {
                        if ((NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTimeout__Stop()).isTrue()&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTimeout__SetTimeoutFlag()).isTrue())||(((((NodeState.FINISHED.equalTo(STATE___DriveToTarget__Drive()).isTrue()&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTimeout()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTarget()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakeNavcam()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakePancam()).isTrue())||getInterface().evalAncestorEnd().isTrue())) {
                            /*
(State #1) priority 4 ----> 
DriveToTarget__StopForTimeout__Stop : WAITING (4) -> FINISHED
<ANCESTOR_ENDS_DISJOINED T?> (FINISHED == DriveToTarget__StopForTimeout__Stop.state && FINISHED == DriveToTarget__StopForTimeout__SetTimeoutFlag.state || FINISHED == DriveToTarget__Drive.state && FINISHED == DriveToTarget__StopForTimeout.state && FINISHED == DriveToTarget__StopForTarget.state && FINISHED == DriveToTarget__TakeNavcam.state && FINISHED == DriveToTarget__TakePancam.state || <root node's ancestor end condition>)
[ Set DriveToTarget__StopForTimeout__Stop.WAITING.END ]
[ Set DriveToTarget__StopForTimeout__Stop.FINISHED.START ]
[ Set outcome of Stop to SKIPPED ]
 ----> (State #6)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__StopForTimeout__Stop : WAITING (4) -> FINISHED");
                            }
                            DriveToTarget__StopForTimeout__Stop__Stop__outcome.setValue(NodeOutcome.SKIPPED, 1);
                            commitAfterMicroStep(DriveToTarget__StopForTimeout__Stop__Stop__outcome);
                            DriveToTarget__StopForTimeout__Stop__state.setNext(6);
                            commitAfterMicroStep(DriveToTarget__StopForTimeout__Stop__state);
                            changeOccurred();
                        } else {
                            /*
(State #1) priority 6 ----> 
DriveToTarget__StopForTimeout__Stop : WAITING (6) -> EXECUTING
<START_CONDITION T?> (true)
<PRE_CONDITION T?> (true)
[ Set DriveToTarget__StopForTimeout__Stop.WAITING.END ]
[ Set DriveToTarget__StopForTimeout__Stop.EXECUTING.START ]
 ----> (State #2)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__StopForTimeout__Stop : WAITING (6) -> EXECUTING");
                            }
                            getWorld().command(DriveToTarget__StopForTimeout__Stop__command_handle, StringValue.get(("rover_stop")));
                            endMacroStep();
                            DriveToTarget__StopForTimeout__Stop__state.setNext(2);
                            commitAfterMicroStep(DriveToTarget__StopForTimeout__Stop__state);
                            changeOccurred();
                        }
                    }
                }
                break;
            case  2 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #2) priority 1 ----> 
DriveToTarget__StopForTimeout__Stop : EXECUTING (1) -> FAILING
<ANCESTOR_EXITS_DISJOINED T?> (false || false || <root node's ancestor exit condition>)
[ Set DriveToTarget__StopForTimeout__Stop.EXECUTING.END ]
[ Set DriveToTarget__StopForTimeout__Stop.FAILING.START ]
[ Set outcome of Stop to INTERRUPTED, failure type PARENT_EXITED ]
 ----> (State #5)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__StopForTimeout__Stop : EXECUTING (1) -> FAILING");
                    }
                    DriveToTarget__StopForTimeout__Stop__Stop__outcome.setValue(NodeOutcome.INTERRUPTED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__Stop__Stop__outcome);
                    DriveToTarget__StopForTimeout__Stop__Stop__failure.setValue(NodeFailureType.PARENT_EXITED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__Stop__Stop__failure);
                    DriveToTarget__StopForTimeout__Stop__state.setNext(5);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__Stop__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #2) priority 3 ----> 
DriveToTarget__StopForTimeout__Stop : EXECUTING (3) -> FAILING
<ANCESTOR_INVARIANTS_CONJOINED F?> (true && true && true && <root node's ancestor invariant condition>)
[ Set DriveToTarget__StopForTimeout__Stop.EXECUTING.END ]
[ Set DriveToTarget__StopForTimeout__Stop.FAILING.START ]
[ Set outcome of Stop to FAILURE, failure type PARENT_FAILED ]
 ----> (State #5)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__StopForTimeout__Stop : EXECUTING (3) -> FAILING");
                        }
                        DriveToTarget__StopForTimeout__Stop__Stop__outcome.setValue(NodeOutcome.FAILURE, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTimeout__Stop__Stop__outcome);
                        DriveToTarget__StopForTimeout__Stop__Stop__failure.setValue(NodeFailureType.PARENT_FAILED, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTimeout__Stop__Stop__failure);
                        DriveToTarget__StopForTimeout__Stop__state.setNext(5);
                        commitAfterMicroStep(DriveToTarget__StopForTimeout__Stop__state);
                        changeOccurred();
                    } else {
                        if (BooleanValue.get(DriveToTarget__StopForTimeout__Stop__command_handle.getCommandHandle().isKnown()).isTrue()) {
                            /*
(State #2) priority 5 ----> 
DriveToTarget__StopForTimeout__Stop : EXECUTING (5) -> FINISHING
<END_CONDITION T?> (isKnown(DriveToTarget__StopForTimeout__Stop.command_handle))
[ Set DriveToTarget__StopForTimeout__Stop.EXECUTING.END ]
[ Set DriveToTarget__StopForTimeout__Stop.FINISHING.START ]
 ----> (State #3)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__StopForTimeout__Stop : EXECUTING (5) -> FINISHING");
                            }
                            DriveToTarget__StopForTimeout__Stop__state.setNext(3);
                            commitAfterMicroStep(DriveToTarget__StopForTimeout__Stop__state);
                            changeOccurred();
                        }
                    }
                }
                break;
            case  3 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #3) priority 1 ----> 
DriveToTarget__StopForTimeout__Stop : FINISHING (1) -> FAILING
<ANCESTOR_EXITS_DISJOINED T?> (false || false || <root node's ancestor exit condition>)
[ Set DriveToTarget__StopForTimeout__Stop.FINISHING.END ]
[ Set DriveToTarget__StopForTimeout__Stop.FAILING.START ]
[ Set outcome of Stop to INTERRUPTED, failure type PARENT_EXITED ]
 ----> (State #5)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__StopForTimeout__Stop : FINISHING (1) -> FAILING");
                    }
                    DriveToTarget__StopForTimeout__Stop__Stop__outcome.setValue(NodeOutcome.INTERRUPTED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__Stop__Stop__outcome);
                    DriveToTarget__StopForTimeout__Stop__Stop__failure.setValue(NodeFailureType.PARENT_EXITED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__Stop__Stop__failure);
                    DriveToTarget__StopForTimeout__Stop__state.setNext(5);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__Stop__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #3) priority 3 ----> 
DriveToTarget__StopForTimeout__Stop : FINISHING (3) -> FAILING
<ANCESTOR_INVARIANTS_CONJOINED F?> (true && true && true && <root node's ancestor invariant condition>)
[ Set DriveToTarget__StopForTimeout__Stop.FINISHING.END ]
[ Set DriveToTarget__StopForTimeout__Stop.FAILING.START ]
[ Set outcome of Stop to FAILURE, failure type PARENT_FAILED ]
 ----> (State #5)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__StopForTimeout__Stop : FINISHING (3) -> FAILING");
                        }
                        DriveToTarget__StopForTimeout__Stop__Stop__outcome.setValue(NodeOutcome.FAILURE, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTimeout__Stop__Stop__outcome);
                        DriveToTarget__StopForTimeout__Stop__Stop__failure.setValue(NodeFailureType.PARENT_FAILED, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTimeout__Stop__Stop__failure);
                        DriveToTarget__StopForTimeout__Stop__state.setNext(5);
                        commitAfterMicroStep(DriveToTarget__StopForTimeout__Stop__state);
                        changeOccurred();
                    } else {
                        if (BooleanValue.get(DriveToTarget__StopForTimeout__Stop__command_handle.getCommandHandle().isKnown()).isTrue()) {
                            /*
(State #3) priority 5 ----> 
DriveToTarget__StopForTimeout__Stop : FINISHING (5) -> ITERATION_ENDED
<COMMAND_ACCEPTED T?> (isKnown(DriveToTarget__StopForTimeout__Stop.command_handle))
<POST_CONDITION T?> (true)
[ Set DriveToTarget__StopForTimeout__Stop.FINISHING.END ]
[ Set DriveToTarget__StopForTimeout__Stop.ITERATION_ENDED.START ]
[ Set outcome of Stop to SUCCESS ]
 ----> (State #4)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__StopForTimeout__Stop : FINISHING (5) -> ITERATION_ENDED");
                            }
                            DriveToTarget__StopForTimeout__Stop__Stop__outcome.setValue(NodeOutcome.SUCCESS, 1);
                            commitAfterMicroStep(DriveToTarget__StopForTimeout__Stop__Stop__outcome);
                            DriveToTarget__StopForTimeout__Stop__state.setNext(4);
                            commitAfterMicroStep(DriveToTarget__StopForTimeout__Stop__state);
                            changeOccurred();
                        }
                    }
                }
                break;
            case  4 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #4) priority 1 ----> 
DriveToTarget__StopForTimeout__Stop : ITERATION_ENDED (1) -> FINISHED
<ANCESTOR_EXITS_DISJOINED T?> (false || false || <root node's ancestor exit condition>)
[ Set DriveToTarget__StopForTimeout__Stop.ITERATION_ENDED.END ]
[ Set DriveToTarget__StopForTimeout__Stop.FINISHED.START ]
[ Set outcome of Stop to INTERRUPTED, failure type PARENT_EXITED ]
 ----> (State #6)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__StopForTimeout__Stop : ITERATION_ENDED (1) -> FINISHED");
                    }
                    DriveToTarget__StopForTimeout__Stop__Stop__outcome.setValue(NodeOutcome.INTERRUPTED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__Stop__Stop__outcome);
                    DriveToTarget__StopForTimeout__Stop__Stop__failure.setValue(NodeFailureType.PARENT_EXITED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__Stop__Stop__failure);
                    DriveToTarget__StopForTimeout__Stop__state.setNext(6);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__Stop__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #4) priority 2 ----> 
DriveToTarget__StopForTimeout__Stop : ITERATION_ENDED (2) -> FINISHED
<ANCESTOR_INVARIANTS_CONJOINED F?> (true && true && true && <root node's ancestor invariant condition>)
[ Set DriveToTarget__StopForTimeout__Stop.ITERATION_ENDED.END ]
[ Set DriveToTarget__StopForTimeout__Stop.FINISHED.START ]
[ Set outcome of Stop to FAILURE, failure type PARENT_FAILED ]
 ----> (State #6)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__StopForTimeout__Stop : ITERATION_ENDED (2) -> FINISHED");
                        }
                        DriveToTarget__StopForTimeout__Stop__Stop__outcome.setValue(NodeOutcome.FAILURE, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTimeout__Stop__Stop__outcome);
                        DriveToTarget__StopForTimeout__Stop__Stop__failure.setValue(NodeFailureType.PARENT_FAILED, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTimeout__Stop__Stop__failure);
                        DriveToTarget__StopForTimeout__Stop__state.setNext(6);
                        commitAfterMicroStep(DriveToTarget__StopForTimeout__Stop__state);
                        changeOccurred();
                    } else {
                        if ((NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTimeout__Stop()).isTrue()&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTimeout__SetTimeoutFlag()).isTrue())||(((((NodeState.FINISHED.equalTo(STATE___DriveToTarget__Drive()).isTrue()&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTimeout()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTarget()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakeNavcam()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakePancam()).isTrue())||getInterface().evalAncestorEnd().isTrue())) {
                            /*
(State #4) priority 3 ----> 
DriveToTarget__StopForTimeout__Stop : ITERATION_ENDED (3) -> FINISHED
<ANCESTOR_ENDS_DISJOINED T?> (FINISHED == DriveToTarget__StopForTimeout__Stop.state && FINISHED == DriveToTarget__StopForTimeout__SetTimeoutFlag.state || FINISHED == DriveToTarget__Drive.state && FINISHED == DriveToTarget__StopForTimeout.state && FINISHED == DriveToTarget__StopForTarget.state && FINISHED == DriveToTarget__TakeNavcam.state && FINISHED == DriveToTarget__TakePancam.state || <root node's ancestor end condition>)
[ Set DriveToTarget__StopForTimeout__Stop.ITERATION_ENDED.END ]
[ Set DriveToTarget__StopForTimeout__Stop.FINISHED.START ]
 ----> (State #6)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__StopForTimeout__Stop : ITERATION_ENDED (3) -> FINISHED");
                            }
                            DriveToTarget__StopForTimeout__Stop__state.setNext(6);
                            commitAfterMicroStep(DriveToTarget__StopForTimeout__Stop__state);
                            changeOccurred();
                        } else {
                            /*
(State #4) priority 4 ----> 
DriveToTarget__StopForTimeout__Stop : ITERATION_ENDED (4) -> FINISHED
<REPEAT_CONDITION F?> (false)
[ Set DriveToTarget__StopForTimeout__Stop.ITERATION_ENDED.END ]
[ Set DriveToTarget__StopForTimeout__Stop.FINISHED.START ]
 ----> (State #6)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__StopForTimeout__Stop : ITERATION_ENDED (4) -> FINISHED");
                            }
                            DriveToTarget__StopForTimeout__Stop__state.setNext(6);
                            commitAfterMicroStep(DriveToTarget__StopForTimeout__Stop__state);
                            changeOccurred();
                        }
                    }
                }
                break;
            case  6 :
                if (STATE___DriveToTarget__StopForTimeout().equalTo(NodeState.WAITING).isTrue()) {
                    /*
(State #6) priority 1 ----> 
DriveToTarget__StopForTimeout__Stop : FINISHED (1) -> INACTIVE
<PARENT_WAITING T?> (DriveToTarget__StopForTimeout.state == WAITING)
[ Set DriveToTarget__StopForTimeout__Stop.FINISHED.END ]
[ Set DriveToTarget__StopForTimeout__Stop.INACTIVE.START ]
[ Reset variables: DriveToTarget__StopForTimeout__Stop.EXECUTING.END, DriveToTarget__StopForTimeout__Stop.ITERATION_ENDED.START, Stop.outcome (DriveToTarget__StopForTimeout__Stop), DriveToTarget__StopForTimeout__Stop.INACTIVE.END, DriveToTarget__StopForTimeout__Stop.FAILING.END, DriveToTarget__StopForTimeout__Stop.WAITING.START, DriveToTarget__StopForTimeout__Stop.EXECUTING.START, DriveToTarget__StopForTimeout__Stop.command_handle, DriveToTarget__StopForTimeout__Stop.FAILING.START, DriveToTarget__StopForTimeout__Stop.INACTIVE.START, DriveToTarget__StopForTimeout__Stop.state, DriveToTarget__StopForTimeout__Stop.ITERATION_ENDED.END, DriveToTarget__StopForTimeout__Stop.FINISHING.END, DriveToTarget__StopForTimeout__Stop.FINISHED.END, Stop.failure (DriveToTarget__StopForTimeout__Stop), DriveToTarget__StopForTimeout__Stop.FINISHING.START, DriveToTarget__StopForTimeout__Stop.FINISHED.START, DriveToTarget__StopForTimeout__Stop.WAITING.END, ]
 ----> (State #0)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__StopForTimeout__Stop : FINISHED (1) -> INACTIVE");
                    }
                    DriveToTarget__StopForTimeout__Stop__Stop__outcome.reset();
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__Stop__Stop__outcome);
                    DriveToTarget__StopForTimeout__Stop__command_handle.reset();
                    DriveToTarget__StopForTimeout__Stop__Stop__failure.reset();
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__Stop__Stop__failure);
                    DriveToTarget__StopForTimeout__Stop__state.setNext(0);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__Stop__state);
                    changeOccurred();
                }
                break;
        }
        /* In Actions executed here: */
        switch (DriveToTarget__StopForTimeout__Stop__state.getNext()) {
        }
    }

    public NodeState STATE___DriveToTarget__StopForTimeout__Stop() {
        switch (DriveToTarget__StopForTimeout__Stop__state.getCurrent()) {
            case  3 :
                return NodeState.FINISHING;
            case  4 :
                return NodeState.ITERATION_ENDED;
            case  2 :
                return NodeState.EXECUTING;
            case  5 :
                return NodeState.FAILING;
            case  1 :
                return NodeState.WAITING;
            case  6 :
                return NodeState.FINISHED;
            case  0 :
                return NodeState.INACTIVE;
        }
        throw new RuntimeException("No state mapping found for DriveToTarget__StopForTimeout__Stop");
    }

    void MicroStep___DriveToTarget__StopForTimeout__SetTimeoutFlag() {
        PBoolean temp;
        switch (DriveToTarget__StopForTimeout__SetTimeoutFlag__state.getCurrent()) {
            case  0 :
                if (STATE___DriveToTarget__StopForTimeout().equalTo(NodeState.FINISHED).isTrue()) {
                    /*
(State #0) priority 1 ----> 
DriveToTarget__StopForTimeout__SetTimeoutFlag : INACTIVE (1) -> FINISHED
<PARENT_FINISHED T?> (DriveToTarget__StopForTimeout.state == FINISHED)
[ Set DriveToTarget__StopForTimeout__SetTimeoutFlag.INACTIVE.END ]
[ Set DriveToTarget__StopForTimeout__SetTimeoutFlag.FINISHED.START ]
[ Set outcome of SetTimeoutFlag to SKIPPED ]
 ----> (State #6)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__StopForTimeout__SetTimeoutFlag : INACTIVE (1) -> FINISHED");
                    }
                    DriveToTarget__StopForTimeout__SetTimeoutFlag__SetTimeoutFlag__outcome.setValue(NodeOutcome.SKIPPED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__SetTimeoutFlag__SetTimeoutFlag__outcome);
                    DriveToTarget__StopForTimeout__SetTimeoutFlag__state.setNext(6);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__SetTimeoutFlag__state);
                    changeOccurred();
                } else {
                    if (STATE___DriveToTarget__StopForTimeout().equalTo(NodeState.EXECUTING).isTrue()) {
                        /*
(State #0) priority 1 ----> 
DriveToTarget__StopForTimeout__SetTimeoutFlag : INACTIVE (1) -> WAITING
<PARENT_EXECUTING T?> (DriveToTarget__StopForTimeout.state == EXECUTING)
[ Set DriveToTarget__StopForTimeout__SetTimeoutFlag.INACTIVE.END ]
[ Set DriveToTarget__StopForTimeout__SetTimeoutFlag.WAITING.START ]
 ----> (State #1)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__StopForTimeout__SetTimeoutFlag : INACTIVE (1) -> WAITING");
                        }
                        DriveToTarget__StopForTimeout__SetTimeoutFlag__state.setNext(1);
                        commitAfterMicroStep(DriveToTarget__StopForTimeout__SetTimeoutFlag__state);
                        changeOccurred();
                    }
                }
                break;
            case  1 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #1) priority 1 ----> 
DriveToTarget__StopForTimeout__SetTimeoutFlag : WAITING (1) -> FINISHED
<ANCESTOR_EXITS_DISJOINED T?> (false || false || <root node's ancestor exit condition>)
[ Set DriveToTarget__StopForTimeout__SetTimeoutFlag.WAITING.END ]
[ Set DriveToTarget__StopForTimeout__SetTimeoutFlag.FINISHED.START ]
[ Set outcome of SetTimeoutFlag to SKIPPED ]
 ----> (State #6)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__StopForTimeout__SetTimeoutFlag : WAITING (1) -> FINISHED");
                    }
                    DriveToTarget__StopForTimeout__SetTimeoutFlag__SetTimeoutFlag__outcome.setValue(NodeOutcome.SKIPPED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__SetTimeoutFlag__SetTimeoutFlag__outcome);
                    DriveToTarget__StopForTimeout__SetTimeoutFlag__state.setNext(6);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__SetTimeoutFlag__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #1) priority 3 ----> 
DriveToTarget__StopForTimeout__SetTimeoutFlag : WAITING (3) -> FINISHED
<ANCESTOR_INVARIANTS_CONJOINED F?> (true && true && true && <root node's ancestor invariant condition>)
[ Set DriveToTarget__StopForTimeout__SetTimeoutFlag.WAITING.END ]
[ Set DriveToTarget__StopForTimeout__SetTimeoutFlag.FINISHED.START ]
[ Set outcome of SetTimeoutFlag to SKIPPED ]
 ----> (State #6)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__StopForTimeout__SetTimeoutFlag : WAITING (3) -> FINISHED");
                        }
                        DriveToTarget__StopForTimeout__SetTimeoutFlag__SetTimeoutFlag__outcome.setValue(NodeOutcome.SKIPPED, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTimeout__SetTimeoutFlag__SetTimeoutFlag__outcome);
                        DriveToTarget__StopForTimeout__SetTimeoutFlag__state.setNext(6);
                        commitAfterMicroStep(DriveToTarget__StopForTimeout__SetTimeoutFlag__state);
                        changeOccurred();
                    } else {
                        if ((NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTimeout__Stop()).isTrue()&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTimeout__SetTimeoutFlag()).isTrue())||(((((NodeState.FINISHED.equalTo(STATE___DriveToTarget__Drive()).isTrue()&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTimeout()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTarget()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakeNavcam()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakePancam()).isTrue())||getInterface().evalAncestorEnd().isTrue())) {
                            /*
(State #1) priority 4 ----> 
DriveToTarget__StopForTimeout__SetTimeoutFlag : WAITING (4) -> FINISHED
<ANCESTOR_ENDS_DISJOINED T?> (FINISHED == DriveToTarget__StopForTimeout__Stop.state && FINISHED == DriveToTarget__StopForTimeout__SetTimeoutFlag.state || FINISHED == DriveToTarget__Drive.state && FINISHED == DriveToTarget__StopForTimeout.state && FINISHED == DriveToTarget__StopForTarget.state && FINISHED == DriveToTarget__TakeNavcam.state && FINISHED == DriveToTarget__TakePancam.state || <root node's ancestor end condition>)
[ Set DriveToTarget__StopForTimeout__SetTimeoutFlag.WAITING.END ]
[ Set DriveToTarget__StopForTimeout__SetTimeoutFlag.FINISHED.START ]
[ Set outcome of SetTimeoutFlag to SKIPPED ]
 ----> (State #6)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__StopForTimeout__SetTimeoutFlag : WAITING (4) -> FINISHED");
                            }
                            DriveToTarget__StopForTimeout__SetTimeoutFlag__SetTimeoutFlag__outcome.setValue(NodeOutcome.SKIPPED, 1);
                            commitAfterMicroStep(DriveToTarget__StopForTimeout__SetTimeoutFlag__SetTimeoutFlag__outcome);
                            DriveToTarget__StopForTimeout__SetTimeoutFlag__state.setNext(6);
                            commitAfterMicroStep(DriveToTarget__StopForTimeout__SetTimeoutFlag__state);
                            changeOccurred();
                        } else {
                            /*
(State #1) priority 6 ----> 
DriveToTarget__StopForTimeout__SetTimeoutFlag : WAITING (6) -> EXECUTING
<START_CONDITION T?> (true)
<PRE_CONDITION T?> (true)
[ Set DriveToTarget__StopForTimeout__SetTimeoutFlag.WAITING.END ]
[ Set DriveToTarget__StopForTimeout__SetTimeoutFlag.EXECUTING.START ]
 ----> (State #2)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__StopForTimeout__SetTimeoutFlag : WAITING (6) -> EXECUTING");
                            }
                            DriveToTarget__timeout.setValue(BooleanValue.get((true)), 2147483647);
                            commitAfterMacroStep(DriveToTarget__timeout);
                            endMacroStep();
                            PREV_VALUE___DriveToTarget__StopForTimeout__SetTimeoutFlag = DriveToTarget__timeout.getValue();
                            DriveToTarget__StopForTimeout__SetTimeoutFlag__state.setNext(2);
                            commitAfterMicroStep(DriveToTarget__StopForTimeout__SetTimeoutFlag__state);
                            changeOccurred();
                        }
                    }
                }
                break;
            case  2 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #2) priority 1 ----> 
DriveToTarget__StopForTimeout__SetTimeoutFlag : EXECUTING (1) -> FAILING
<ANCESTOR_EXITS_DISJOINED T?> (false || false || <root node's ancestor exit condition>)
[ Set DriveToTarget__StopForTimeout__SetTimeoutFlag.EXECUTING.END ]
[ Set DriveToTarget__StopForTimeout__SetTimeoutFlag.FAILING.START ]
[ Set outcome of SetTimeoutFlag to INTERRUPTED, failure type PARENT_EXITED ]
 ----> (State #5)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__StopForTimeout__SetTimeoutFlag : EXECUTING (1) -> FAILING");
                    }
                    DriveToTarget__StopForTimeout__SetTimeoutFlag__SetTimeoutFlag__outcome.setValue(NodeOutcome.INTERRUPTED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__SetTimeoutFlag__SetTimeoutFlag__outcome);
                    DriveToTarget__StopForTimeout__SetTimeoutFlag__SetTimeoutFlag__failure.setValue(NodeFailureType.PARENT_EXITED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__SetTimeoutFlag__SetTimeoutFlag__failure);
                    DriveToTarget__timeout.setValue(PREV_VALUE___DriveToTarget__StopForTimeout__SetTimeoutFlag, 2147483647);
                    commitAfterMacroStep(DriveToTarget__timeout);
                    endMacroStep();
                    DriveToTarget__StopForTimeout__SetTimeoutFlag__state.setNext(5);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__SetTimeoutFlag__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #2) priority 3 ----> 
DriveToTarget__StopForTimeout__SetTimeoutFlag : EXECUTING (3) -> FAILING
<ANCESTOR_INVARIANTS_CONJOINED F?> (true && true && true && <root node's ancestor invariant condition>)
[ Set DriveToTarget__StopForTimeout__SetTimeoutFlag.EXECUTING.END ]
[ Set DriveToTarget__StopForTimeout__SetTimeoutFlag.FAILING.START ]
[ Set outcome of SetTimeoutFlag to FAILURE, failure type PARENT_FAILED ]
 ----> (State #5)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__StopForTimeout__SetTimeoutFlag : EXECUTING (3) -> FAILING");
                        }
                        DriveToTarget__StopForTimeout__SetTimeoutFlag__SetTimeoutFlag__outcome.setValue(NodeOutcome.FAILURE, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTimeout__SetTimeoutFlag__SetTimeoutFlag__outcome);
                        DriveToTarget__StopForTimeout__SetTimeoutFlag__SetTimeoutFlag__failure.setValue(NodeFailureType.PARENT_FAILED, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTimeout__SetTimeoutFlag__SetTimeoutFlag__failure);
                        DriveToTarget__timeout.setValue(PREV_VALUE___DriveToTarget__StopForTimeout__SetTimeoutFlag, 2147483647);
                        commitAfterMacroStep(DriveToTarget__timeout);
                        endMacroStep();
                        DriveToTarget__StopForTimeout__SetTimeoutFlag__state.setNext(5);
                        commitAfterMicroStep(DriveToTarget__StopForTimeout__SetTimeoutFlag__state);
                        changeOccurred();
                    } else {
                        /*
(State #2) priority 5 ----> 
DriveToTarget__StopForTimeout__SetTimeoutFlag : EXECUTING (5) -> ITERATION_ENDED
<END_CONDITION T?> (true)
<POST_CONDITION T?> (true)
[ Set DriveToTarget__StopForTimeout__SetTimeoutFlag.EXECUTING.END ]
[ Set DriveToTarget__StopForTimeout__SetTimeoutFlag.ITERATION_ENDED.START ]
[ Set outcome of SetTimeoutFlag to SUCCESS ]
 ----> (State #4)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__StopForTimeout__SetTimeoutFlag : EXECUTING (5) -> ITERATION_ENDED");
                        }
                        DriveToTarget__StopForTimeout__SetTimeoutFlag__SetTimeoutFlag__outcome.setValue(NodeOutcome.SUCCESS, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTimeout__SetTimeoutFlag__SetTimeoutFlag__outcome);
                        DriveToTarget__StopForTimeout__SetTimeoutFlag__state.setNext(4);
                        commitAfterMicroStep(DriveToTarget__StopForTimeout__SetTimeoutFlag__state);
                        changeOccurred();
                    }
                }
                break;
            case  4 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #4) priority 1 ----> 
DriveToTarget__StopForTimeout__SetTimeoutFlag : ITERATION_ENDED (1) -> FINISHED
<ANCESTOR_EXITS_DISJOINED T?> (false || false || <root node's ancestor exit condition>)
[ Set DriveToTarget__StopForTimeout__SetTimeoutFlag.ITERATION_ENDED.END ]
[ Set DriveToTarget__StopForTimeout__SetTimeoutFlag.FINISHED.START ]
[ Set outcome of SetTimeoutFlag to INTERRUPTED, failure type PARENT_EXITED ]
 ----> (State #6)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__StopForTimeout__SetTimeoutFlag : ITERATION_ENDED (1) -> FINISHED");
                    }
                    DriveToTarget__StopForTimeout__SetTimeoutFlag__SetTimeoutFlag__outcome.setValue(NodeOutcome.INTERRUPTED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__SetTimeoutFlag__SetTimeoutFlag__outcome);
                    DriveToTarget__StopForTimeout__SetTimeoutFlag__SetTimeoutFlag__failure.setValue(NodeFailureType.PARENT_EXITED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__SetTimeoutFlag__SetTimeoutFlag__failure);
                    DriveToTarget__StopForTimeout__SetTimeoutFlag__state.setNext(6);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__SetTimeoutFlag__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #4) priority 2 ----> 
DriveToTarget__StopForTimeout__SetTimeoutFlag : ITERATION_ENDED (2) -> FINISHED
<ANCESTOR_INVARIANTS_CONJOINED F?> (true && true && true && <root node's ancestor invariant condition>)
[ Set DriveToTarget__StopForTimeout__SetTimeoutFlag.ITERATION_ENDED.END ]
[ Set DriveToTarget__StopForTimeout__SetTimeoutFlag.FINISHED.START ]
[ Set outcome of SetTimeoutFlag to FAILURE, failure type PARENT_FAILED ]
 ----> (State #6)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__StopForTimeout__SetTimeoutFlag : ITERATION_ENDED (2) -> FINISHED");
                        }
                        DriveToTarget__StopForTimeout__SetTimeoutFlag__SetTimeoutFlag__outcome.setValue(NodeOutcome.FAILURE, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTimeout__SetTimeoutFlag__SetTimeoutFlag__outcome);
                        DriveToTarget__StopForTimeout__SetTimeoutFlag__SetTimeoutFlag__failure.setValue(NodeFailureType.PARENT_FAILED, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTimeout__SetTimeoutFlag__SetTimeoutFlag__failure);
                        DriveToTarget__StopForTimeout__SetTimeoutFlag__state.setNext(6);
                        commitAfterMicroStep(DriveToTarget__StopForTimeout__SetTimeoutFlag__state);
                        changeOccurred();
                    } else {
                        if ((NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTimeout__Stop()).isTrue()&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTimeout__SetTimeoutFlag()).isTrue())||(((((NodeState.FINISHED.equalTo(STATE___DriveToTarget__Drive()).isTrue()&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTimeout()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTarget()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakeNavcam()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakePancam()).isTrue())||getInterface().evalAncestorEnd().isTrue())) {
                            /*
(State #4) priority 3 ----> 
DriveToTarget__StopForTimeout__SetTimeoutFlag : ITERATION_ENDED (3) -> FINISHED
<ANCESTOR_ENDS_DISJOINED T?> (FINISHED == DriveToTarget__StopForTimeout__Stop.state && FINISHED == DriveToTarget__StopForTimeout__SetTimeoutFlag.state || FINISHED == DriveToTarget__Drive.state && FINISHED == DriveToTarget__StopForTimeout.state && FINISHED == DriveToTarget__StopForTarget.state && FINISHED == DriveToTarget__TakeNavcam.state && FINISHED == DriveToTarget__TakePancam.state || <root node's ancestor end condition>)
[ Set DriveToTarget__StopForTimeout__SetTimeoutFlag.ITERATION_ENDED.END ]
[ Set DriveToTarget__StopForTimeout__SetTimeoutFlag.FINISHED.START ]
 ----> (State #6)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__StopForTimeout__SetTimeoutFlag : ITERATION_ENDED (3) -> FINISHED");
                            }
                            DriveToTarget__StopForTimeout__SetTimeoutFlag__state.setNext(6);
                            commitAfterMicroStep(DriveToTarget__StopForTimeout__SetTimeoutFlag__state);
                            changeOccurred();
                        } else {
                            /*
(State #4) priority 4 ----> 
DriveToTarget__StopForTimeout__SetTimeoutFlag : ITERATION_ENDED (4) -> FINISHED
<REPEAT_CONDITION F?> (false)
[ Set DriveToTarget__StopForTimeout__SetTimeoutFlag.ITERATION_ENDED.END ]
[ Set DriveToTarget__StopForTimeout__SetTimeoutFlag.FINISHED.START ]
 ----> (State #6)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__StopForTimeout__SetTimeoutFlag : ITERATION_ENDED (4) -> FINISHED");
                            }
                            DriveToTarget__StopForTimeout__SetTimeoutFlag__state.setNext(6);
                            commitAfterMicroStep(DriveToTarget__StopForTimeout__SetTimeoutFlag__state);
                            changeOccurred();
                        }
                    }
                }
                break;
            case  6 :
                if (STATE___DriveToTarget__StopForTimeout().equalTo(NodeState.WAITING).isTrue()) {
                    /*
(State #6) priority 1 ----> 
DriveToTarget__StopForTimeout__SetTimeoutFlag : FINISHED (1) -> INACTIVE
<PARENT_WAITING T?> (DriveToTarget__StopForTimeout.state == WAITING)
[ Set DriveToTarget__StopForTimeout__SetTimeoutFlag.FINISHED.END ]
[ Set DriveToTarget__StopForTimeout__SetTimeoutFlag.INACTIVE.START ]
[ Reset variables: DriveToTarget__StopForTimeout__SetTimeoutFlag.EXECUTING.END, DriveToTarget__StopForTimeout__SetTimeoutFlag.ITERATION_ENDED.START, SetTimeoutFlag.outcome (DriveToTarget__StopForTimeout__SetTimeoutFlag), DriveToTarget__StopForTimeout__SetTimeoutFlag.INACTIVE.END, DriveToTarget__StopForTimeout__SetTimeoutFlag.FAILING.END, DriveToTarget__StopForTimeout__SetTimeoutFlag.WAITING.START, DriveToTarget__StopForTimeout__SetTimeoutFlag.EXECUTING.START, Previous value of DriveToTarget__StopForTimeout__SetTimeoutFlag, DriveToTarget__StopForTimeout__SetTimeoutFlag.FAILING.START, DriveToTarget__StopForTimeout__SetTimeoutFlag.INACTIVE.START, DriveToTarget__StopForTimeout__SetTimeoutFlag.state, DriveToTarget__StopForTimeout__SetTimeoutFlag.ITERATION_ENDED.END, DriveToTarget__StopForTimeout__SetTimeoutFlag.FINISHING.END, DriveToTarget__StopForTimeout__SetTimeoutFlag.FINISHED.END, SetTimeoutFlag.failure (DriveToTarget__StopForTimeout__SetTimeoutFlag), DriveToTarget__StopForTimeout__SetTimeoutFlag.FINISHING.START, DriveToTarget__StopForTimeout__SetTimeoutFlag.FINISHED.START, DriveToTarget__StopForTimeout__SetTimeoutFlag.WAITING.END, ]
 ----> (State #0)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__StopForTimeout__SetTimeoutFlag : FINISHED (1) -> INACTIVE");
                    }
                    DriveToTarget__StopForTimeout__SetTimeoutFlag__SetTimeoutFlag__outcome.reset();
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__SetTimeoutFlag__SetTimeoutFlag__outcome);
                    PREV_VALUE___DriveToTarget__StopForTimeout__SetTimeoutFlag = null;
                    DriveToTarget__StopForTimeout__SetTimeoutFlag__SetTimeoutFlag__failure.reset();
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__SetTimeoutFlag__SetTimeoutFlag__failure);
                    DriveToTarget__StopForTimeout__SetTimeoutFlag__state.setNext(0);
                    commitAfterMicroStep(DriveToTarget__StopForTimeout__SetTimeoutFlag__state);
                    changeOccurred();
                }
                break;
        }
        /* In Actions executed here: */
        switch (DriveToTarget__StopForTimeout__SetTimeoutFlag__state.getNext()) {
        }
    }

    public NodeState STATE___DriveToTarget__StopForTimeout__SetTimeoutFlag() {
        switch (DriveToTarget__StopForTimeout__SetTimeoutFlag__state.getCurrent()) {
            case  3 :
                return NodeState.FINISHING;
            case  4 :
                return NodeState.ITERATION_ENDED;
            case  2 :
                return NodeState.EXECUTING;
            case  5 :
                return NodeState.FAILING;
            case  1 :
                return NodeState.WAITING;
            case  6 :
                return NodeState.FINISHED;
            case  0 :
                return NodeState.INACTIVE;
        }
        throw new RuntimeException("No state mapping found for DriveToTarget__StopForTimeout__SetTimeoutFlag");
    }

    void MicroStep___DriveToTarget__StopForTarget() {
        PBoolean temp;
        switch (DriveToTarget__StopForTarget__state.getCurrent()) {
            case  0 :
                if (STATE___DriveToTarget().equalTo(NodeState.FINISHED).isTrue()) {
                    /*
(State #0) priority 1 ----> 
DriveToTarget__StopForTarget : INACTIVE (1) -> FINISHED
<PARENT_FINISHED T?> (DriveToTarget.state == FINISHED)
[ Set DriveToTarget__StopForTarget.INACTIVE.END ]
[ Set DriveToTarget__StopForTarget.FINISHED.START ]
[ Set outcome of StopForTarget to SKIPPED ]
 ----> (State #6)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__StopForTarget : INACTIVE (1) -> FINISHED");
                    }
                    DriveToTarget__StopForTarget__StopForTarget__outcome.setValue(NodeOutcome.SKIPPED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__StopForTarget__outcome);
                    DriveToTarget__StopForTarget__state.setNext(6);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__state);
                    changeOccurred();
                } else {
                    if (STATE___DriveToTarget().equalTo(NodeState.EXECUTING).isTrue()) {
                        /*
(State #0) priority 1 ----> 
DriveToTarget__StopForTarget : INACTIVE (1) -> WAITING
<PARENT_EXECUTING T?> (DriveToTarget.state == EXECUTING)
[ Set DriveToTarget__StopForTarget.INACTIVE.END ]
[ Set DriveToTarget__StopForTarget.WAITING.START ]
 ----> (State #1)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__StopForTarget : INACTIVE (1) -> WAITING");
                        }
                        DriveToTarget__StopForTarget__state.setNext(1);
                        commitAfterMicroStep(DriveToTarget__StopForTarget__state);
                        changeOccurred();
                    }
                }
                break;
            case  1 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #1) priority 1 ----> 
DriveToTarget__StopForTarget : WAITING (1) -> FINISHED
<ANCESTOR_EXITS_DISJOINED T?> (false || <root node's ancestor exit condition>)
[ Set DriveToTarget__StopForTarget.WAITING.END ]
[ Set DriveToTarget__StopForTarget.FINISHED.START ]
[ Set outcome of StopForTarget to SKIPPED ]
 ----> (State #6)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__StopForTarget : WAITING (1) -> FINISHED");
                    }
                    DriveToTarget__StopForTarget__StopForTarget__outcome.setValue(NodeOutcome.SKIPPED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__StopForTarget__outcome);
                    DriveToTarget__StopForTarget__state.setNext(6);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #1) priority 3 ----> 
DriveToTarget__StopForTarget : WAITING (3) -> FINISHED
<ANCESTOR_INVARIANTS_CONJOINED F?> (true && true && <root node's ancestor invariant condition>)
[ Set DriveToTarget__StopForTarget.WAITING.END ]
[ Set DriveToTarget__StopForTarget.FINISHED.START ]
[ Set outcome of StopForTarget to SKIPPED ]
 ----> (State #6)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__StopForTarget : WAITING (3) -> FINISHED");
                        }
                        DriveToTarget__StopForTarget__StopForTarget__outcome.setValue(NodeOutcome.SKIPPED, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTarget__StopForTarget__outcome);
                        DriveToTarget__StopForTarget__state.setNext(6);
                        commitAfterMicroStep(DriveToTarget__StopForTarget__state);
                        changeOccurred();
                    } else {
                        if (((((NodeState.FINISHED.equalTo(STATE___DriveToTarget__Drive()).isTrue()&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTimeout()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTarget()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakeNavcam()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakePancam()).isTrue())||getInterface().evalAncestorEnd().isTrue()) {
                            /*
(State #1) priority 4 ----> 
DriveToTarget__StopForTarget : WAITING (4) -> FINISHED
<ANCESTOR_ENDS_DISJOINED T?> (FINISHED == DriveToTarget__Drive.state && FINISHED == DriveToTarget__StopForTimeout.state && FINISHED == DriveToTarget__StopForTarget.state && FINISHED == DriveToTarget__TakeNavcam.state && FINISHED == DriveToTarget__TakePancam.state || <root node's ancestor end condition>)
[ Set DriveToTarget__StopForTarget.WAITING.END ]
[ Set DriveToTarget__StopForTarget.FINISHED.START ]
[ Set outcome of StopForTarget to SKIPPED ]
 ----> (State #6)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__StopForTarget : WAITING (4) -> FINISHED");
                            }
                            DriveToTarget__StopForTarget__StopForTarget__outcome.setValue(NodeOutcome.SKIPPED, 1);
                            commitAfterMicroStep(DriveToTarget__StopForTarget__StopForTarget__outcome);
                            DriveToTarget__StopForTarget__state.setNext(6);
                            commitAfterMicroStep(DriveToTarget__StopForTarget__state);
                            changeOccurred();
                        } else {
                            if (DriveToTarget__timeout.getValue().isTrue()) {
                                /*
(State #1) priority 5 ----> 
DriveToTarget__StopForTarget : WAITING (5) -> FINISHED
<SKIP_CONDITION T?> (timeout (DriveToTarget))
[ Set DriveToTarget__StopForTarget.WAITING.END ]
[ Set DriveToTarget__StopForTarget.FINISHED.START ]
[ Set outcome of StopForTarget to SKIPPED ]
 ----> (State #6)
*/
                                if (JavaPlan.DEBUG) {
                                    System.out.println("DriveToTarget__StopForTarget : WAITING (5) -> FINISHED");
                                }
                                DriveToTarget__StopForTarget__StopForTarget__outcome.setValue(NodeOutcome.SKIPPED, 1);
                                commitAfterMicroStep(DriveToTarget__StopForTarget__StopForTarget__outcome);
                                DriveToTarget__StopForTarget__state.setNext(6);
                                commitAfterMicroStep(DriveToTarget__StopForTarget__state);
                                changeOccurred();
                            } else {
                                if (((PBoolean) getWorld().lookupOnChange(StringValue.get(("target_in_view")), RealValue.get((0.0)))).isTrue()) {
                                    /*
(State #1) priority 6 ----> 
DriveToTarget__StopForTarget : WAITING (6) -> EXECUTING
<START_CONDITION T?> ((PBoolean) (LookupOnChange("target_in_view", 0.0)))
<PRE_CONDITION T?> (true)
[ Set DriveToTarget__StopForTarget.WAITING.END ]
[ Set DriveToTarget__StopForTarget.EXECUTING.START ]
 ----> (State #2)
*/
                                    if (JavaPlan.DEBUG) {
                                        System.out.println("DriveToTarget__StopForTarget : WAITING (6) -> EXECUTING");
                                    }
                                    DriveToTarget__StopForTarget__state.setNext(2);
                                    commitAfterMicroStep(DriveToTarget__StopForTarget__state);
                                    changeOccurred();
                                }
                            }
                        }
                    }
                }
                break;
            case  2 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #2) priority 1 ----> 
DriveToTarget__StopForTarget : EXECUTING (1) -> FAILING
<ANCESTOR_EXITS_DISJOINED T?> (false || <root node's ancestor exit condition>)
[ Set DriveToTarget__StopForTarget.EXECUTING.END ]
[ Set DriveToTarget__StopForTarget.FAILING.START ]
[ Set outcome of StopForTarget to INTERRUPTED, failure type PARENT_EXITED ]
 ----> (State #5)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__StopForTarget : EXECUTING (1) -> FAILING");
                    }
                    DriveToTarget__StopForTarget__StopForTarget__outcome.setValue(NodeOutcome.INTERRUPTED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__StopForTarget__outcome);
                    DriveToTarget__StopForTarget__StopForTarget__failure.setValue(NodeFailureType.PARENT_EXITED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__StopForTarget__failure);
                    DriveToTarget__StopForTarget__state.setNext(5);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #2) priority 3 ----> 
DriveToTarget__StopForTarget : EXECUTING (3) -> FAILING
<ANCESTOR_INVARIANTS_CONJOINED F?> (true && true && <root node's ancestor invariant condition>)
[ Set DriveToTarget__StopForTarget.EXECUTING.END ]
[ Set DriveToTarget__StopForTarget.FAILING.START ]
[ Set outcome of StopForTarget to FAILURE, failure type PARENT_FAILED ]
 ----> (State #5)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__StopForTarget : EXECUTING (3) -> FAILING");
                        }
                        DriveToTarget__StopForTarget__StopForTarget__outcome.setValue(NodeOutcome.FAILURE, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTarget__StopForTarget__outcome);
                        DriveToTarget__StopForTarget__StopForTarget__failure.setValue(NodeFailureType.PARENT_FAILED, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTarget__StopForTarget__failure);
                        DriveToTarget__StopForTarget__state.setNext(5);
                        commitAfterMicroStep(DriveToTarget__StopForTarget__state);
                        changeOccurred();
                    } else {
                        if (NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTarget__Stop()).isTrue()&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTarget__SetDriveFlag()).isTrue()) {
                            /*
(State #2) priority 5 ----> 
DriveToTarget__StopForTarget : EXECUTING (5) -> FINISHING
<END_CONDITION T?> (FINISHED == DriveToTarget__StopForTarget__Stop.state && FINISHED == DriveToTarget__StopForTarget__SetDriveFlag.state)
[ Set DriveToTarget__StopForTarget.EXECUTING.END ]
[ Set DriveToTarget__StopForTarget.FINISHING.START ]
 ----> (State #3)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__StopForTarget : EXECUTING (5) -> FINISHING");
                            }
                            DriveToTarget__StopForTarget__state.setNext(3);
                            commitAfterMicroStep(DriveToTarget__StopForTarget__state);
                            changeOccurred();
                        }
                    }
                }
                break;
            case  3 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #3) priority 1 ----> 
DriveToTarget__StopForTarget : FINISHING (1) -> FAILING
<ANCESTOR_EXITS_DISJOINED T?> (false || <root node's ancestor exit condition>)
[ Set DriveToTarget__StopForTarget.FINISHING.END ]
[ Set DriveToTarget__StopForTarget.FAILING.START ]
[ Set outcome of StopForTarget to INTERRUPTED, failure type PARENT_EXITED ]
 ----> (State #5)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__StopForTarget : FINISHING (1) -> FAILING");
                    }
                    DriveToTarget__StopForTarget__StopForTarget__outcome.setValue(NodeOutcome.INTERRUPTED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__StopForTarget__outcome);
                    DriveToTarget__StopForTarget__StopForTarget__failure.setValue(NodeFailureType.PARENT_EXITED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__StopForTarget__failure);
                    DriveToTarget__StopForTarget__state.setNext(5);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #3) priority 3 ----> 
DriveToTarget__StopForTarget : FINISHING (3) -> FAILING
<ANCESTOR_INVARIANTS_CONJOINED F?> (true && true && <root node's ancestor invariant condition>)
[ Set DriveToTarget__StopForTarget.FINISHING.END ]
[ Set DriveToTarget__StopForTarget.FAILING.START ]
[ Set outcome of StopForTarget to FAILURE, failure type PARENT_FAILED ]
 ----> (State #5)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__StopForTarget : FINISHING (3) -> FAILING");
                        }
                        DriveToTarget__StopForTarget__StopForTarget__outcome.setValue(NodeOutcome.FAILURE, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTarget__StopForTarget__outcome);
                        DriveToTarget__StopForTarget__StopForTarget__failure.setValue(NodeFailureType.PARENT_FAILED, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTarget__StopForTarget__failure);
                        DriveToTarget__StopForTarget__state.setNext(5);
                        commitAfterMicroStep(DriveToTarget__StopForTarget__state);
                        changeOccurred();
                    } else {
                        if ((STATE___DriveToTarget__StopForTarget__Stop().equalTo(NodeState.WAITING).isTrue()||STATE___DriveToTarget__StopForTarget__Stop().equalTo(NodeState.FINISHED).isTrue())&&(STATE___DriveToTarget__StopForTarget__SetDriveFlag().equalTo(NodeState.WAITING).isTrue()||STATE___DriveToTarget__StopForTarget__SetDriveFlag().equalTo(NodeState.FINISHED).isTrue())) {
                            /*
(State #3) priority 5 ----> 
DriveToTarget__StopForTarget : FINISHING (5) -> ITERATION_ENDED
<ALL_CHILDREN_WAITING_OR_FINISHED T?> (DriveToTarget__StopForTarget__Stop.state == WAITING || DriveToTarget__StopForTarget__Stop.state == FINISHED && DriveToTarget__StopForTarget__SetDriveFlag.state == WAITING || DriveToTarget__StopForTarget__SetDriveFlag.state == FINISHED)
<POST_CONDITION T?> (true)
[ Set DriveToTarget__StopForTarget.FINISHING.END ]
[ Set DriveToTarget__StopForTarget.ITERATION_ENDED.START ]
[ Set outcome of StopForTarget to SUCCESS ]
 ----> (State #4)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__StopForTarget : FINISHING (5) -> ITERATION_ENDED");
                            }
                            DriveToTarget__StopForTarget__StopForTarget__outcome.setValue(NodeOutcome.SUCCESS, 1);
                            commitAfterMicroStep(DriveToTarget__StopForTarget__StopForTarget__outcome);
                            DriveToTarget__StopForTarget__state.setNext(4);
                            commitAfterMicroStep(DriveToTarget__StopForTarget__state);
                            changeOccurred();
                        }
                    }
                }
                break;
            case  4 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #4) priority 1 ----> 
DriveToTarget__StopForTarget : ITERATION_ENDED (1) -> FINISHED
<ANCESTOR_EXITS_DISJOINED T?> (false || <root node's ancestor exit condition>)
[ Set DriveToTarget__StopForTarget.ITERATION_ENDED.END ]
[ Set DriveToTarget__StopForTarget.FINISHED.START ]
[ Set outcome of StopForTarget to INTERRUPTED, failure type PARENT_EXITED ]
 ----> (State #6)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__StopForTarget : ITERATION_ENDED (1) -> FINISHED");
                    }
                    DriveToTarget__StopForTarget__StopForTarget__outcome.setValue(NodeOutcome.INTERRUPTED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__StopForTarget__outcome);
                    DriveToTarget__StopForTarget__StopForTarget__failure.setValue(NodeFailureType.PARENT_EXITED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__StopForTarget__failure);
                    DriveToTarget__StopForTarget__state.setNext(6);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #4) priority 2 ----> 
DriveToTarget__StopForTarget : ITERATION_ENDED (2) -> FINISHED
<ANCESTOR_INVARIANTS_CONJOINED F?> (true && true && <root node's ancestor invariant condition>)
[ Set DriveToTarget__StopForTarget.ITERATION_ENDED.END ]
[ Set DriveToTarget__StopForTarget.FINISHED.START ]
[ Set outcome of StopForTarget to FAILURE, failure type PARENT_FAILED ]
 ----> (State #6)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__StopForTarget : ITERATION_ENDED (2) -> FINISHED");
                        }
                        DriveToTarget__StopForTarget__StopForTarget__outcome.setValue(NodeOutcome.FAILURE, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTarget__StopForTarget__outcome);
                        DriveToTarget__StopForTarget__StopForTarget__failure.setValue(NodeFailureType.PARENT_FAILED, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTarget__StopForTarget__failure);
                        DriveToTarget__StopForTarget__state.setNext(6);
                        commitAfterMicroStep(DriveToTarget__StopForTarget__state);
                        changeOccurred();
                    } else {
                        if (((((NodeState.FINISHED.equalTo(STATE___DriveToTarget__Drive()).isTrue()&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTimeout()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTarget()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakeNavcam()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakePancam()).isTrue())||getInterface().evalAncestorEnd().isTrue()) {
                            /*
(State #4) priority 3 ----> 
DriveToTarget__StopForTarget : ITERATION_ENDED (3) -> FINISHED
<ANCESTOR_ENDS_DISJOINED T?> (FINISHED == DriveToTarget__Drive.state && FINISHED == DriveToTarget__StopForTimeout.state && FINISHED == DriveToTarget__StopForTarget.state && FINISHED == DriveToTarget__TakeNavcam.state && FINISHED == DriveToTarget__TakePancam.state || <root node's ancestor end condition>)
[ Set DriveToTarget__StopForTarget.ITERATION_ENDED.END ]
[ Set DriveToTarget__StopForTarget.FINISHED.START ]
 ----> (State #6)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__StopForTarget : ITERATION_ENDED (3) -> FINISHED");
                            }
                            DriveToTarget__StopForTarget__state.setNext(6);
                            commitAfterMicroStep(DriveToTarget__StopForTarget__state);
                            changeOccurred();
                        } else {
                            /*
(State #4) priority 4 ----> 
DriveToTarget__StopForTarget : ITERATION_ENDED (4) -> FINISHED
<REPEAT_CONDITION F?> (false)
[ Set DriveToTarget__StopForTarget.ITERATION_ENDED.END ]
[ Set DriveToTarget__StopForTarget.FINISHED.START ]
 ----> (State #6)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__StopForTarget : ITERATION_ENDED (4) -> FINISHED");
                            }
                            DriveToTarget__StopForTarget__state.setNext(6);
                            commitAfterMicroStep(DriveToTarget__StopForTarget__state);
                            changeOccurred();
                        }
                    }
                }
                break;
            case  6 :
                if (STATE___DriveToTarget().equalTo(NodeState.WAITING).isTrue()) {
                    /*
(State #6) priority 1 ----> 
DriveToTarget__StopForTarget : FINISHED (1) -> INACTIVE
<PARENT_WAITING T?> (DriveToTarget.state == WAITING)
[ Set DriveToTarget__StopForTarget.FINISHED.END ]
[ Set DriveToTarget__StopForTarget.INACTIVE.START ]
[ Reset variables: DriveToTarget__StopForTarget.EXECUTING.END, DriveToTarget__StopForTarget.ITERATION_ENDED.START, StopForTarget.outcome (DriveToTarget__StopForTarget), DriveToTarget__StopForTarget.INACTIVE.END, DriveToTarget__StopForTarget.FAILING.END, DriveToTarget__StopForTarget.WAITING.START, DriveToTarget__StopForTarget.EXECUTING.START, DriveToTarget__StopForTarget.FAILING.START, DriveToTarget__StopForTarget.INACTIVE.START, DriveToTarget__StopForTarget.state, DriveToTarget__StopForTarget.ITERATION_ENDED.END, DriveToTarget__StopForTarget.FINISHING.END, DriveToTarget__StopForTarget.FINISHED.END, StopForTarget.failure (DriveToTarget__StopForTarget), DriveToTarget__StopForTarget.FINISHING.START, DriveToTarget__StopForTarget.FINISHED.START, DriveToTarget__StopForTarget.WAITING.END, ]
 ----> (State #0)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__StopForTarget : FINISHED (1) -> INACTIVE");
                    }
                    DriveToTarget__StopForTarget__StopForTarget__outcome.reset();
                    commitAfterMicroStep(DriveToTarget__StopForTarget__StopForTarget__outcome);
                    DriveToTarget__StopForTarget__StopForTarget__failure.reset();
                    commitAfterMicroStep(DriveToTarget__StopForTarget__StopForTarget__failure);
                    DriveToTarget__StopForTarget__state.setNext(0);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__state);
                    changeOccurred();
                }
                break;
        }
        /* In Actions executed here: */
        switch (DriveToTarget__StopForTarget__state.getNext()) {
            case  1 :
                MicroStep___DriveToTarget__StopForTarget__SetDriveFlag();
                MicroStep___DriveToTarget__StopForTarget__Stop();
                break;
            case  2 :
                MicroStep___DriveToTarget__StopForTarget__SetDriveFlag();
                MicroStep___DriveToTarget__StopForTarget__Stop();
                break;
            case  3 :
                MicroStep___DriveToTarget__StopForTarget__SetDriveFlag();
                MicroStep___DriveToTarget__StopForTarget__Stop();
                break;
            case  4 :
                MicroStep___DriveToTarget__StopForTarget__SetDriveFlag();
                MicroStep___DriveToTarget__StopForTarget__Stop();
                break;
            case  5 :
                MicroStep___DriveToTarget__StopForTarget__SetDriveFlag();
                MicroStep___DriveToTarget__StopForTarget__Stop();
                break;
            case  6 :
                MicroStep___DriveToTarget__StopForTarget__SetDriveFlag();
                MicroStep___DriveToTarget__StopForTarget__Stop();
                break;
        }
    }

    public NodeState STATE___DriveToTarget__StopForTarget() {
        switch (DriveToTarget__StopForTarget__state.getCurrent()) {
            case  3 :
                return NodeState.FINISHING;
            case  4 :
                return NodeState.ITERATION_ENDED;
            case  2 :
                return NodeState.EXECUTING;
            case  5 :
                return NodeState.FAILING;
            case  1 :
                return NodeState.WAITING;
            case  6 :
                return NodeState.FINISHED;
            case  0 :
                return NodeState.INACTIVE;
        }
        throw new RuntimeException("No state mapping found for DriveToTarget__StopForTarget");
    }

    void MicroStep___DriveToTarget__StopForTarget__Stop() {
        PBoolean temp;
        switch (DriveToTarget__StopForTarget__Stop__state.getCurrent()) {
            case  0 :
                if (STATE___DriveToTarget__StopForTarget().equalTo(NodeState.FINISHED).isTrue()) {
                    /*
(State #0) priority 1 ----> 
DriveToTarget__StopForTarget__Stop : INACTIVE (1) -> FINISHED
<PARENT_FINISHED T?> (DriveToTarget__StopForTarget.state == FINISHED)
[ Set DriveToTarget__StopForTarget__Stop.INACTIVE.END ]
[ Set DriveToTarget__StopForTarget__Stop.FINISHED.START ]
[ Set outcome of Stop to SKIPPED ]
 ----> (State #6)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__StopForTarget__Stop : INACTIVE (1) -> FINISHED");
                    }
                    DriveToTarget__StopForTarget__Stop__Stop__outcome.setValue(NodeOutcome.SKIPPED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__Stop__Stop__outcome);
                    DriveToTarget__StopForTarget__Stop__state.setNext(6);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__Stop__state);
                    changeOccurred();
                } else {
                    if (STATE___DriveToTarget__StopForTarget().equalTo(NodeState.EXECUTING).isTrue()) {
                        /*
(State #0) priority 1 ----> 
DriveToTarget__StopForTarget__Stop : INACTIVE (1) -> WAITING
<PARENT_EXECUTING T?> (DriveToTarget__StopForTarget.state == EXECUTING)
[ Set DriveToTarget__StopForTarget__Stop.INACTIVE.END ]
[ Set DriveToTarget__StopForTarget__Stop.WAITING.START ]
 ----> (State #1)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__StopForTarget__Stop : INACTIVE (1) -> WAITING");
                        }
                        DriveToTarget__StopForTarget__Stop__state.setNext(1);
                        commitAfterMicroStep(DriveToTarget__StopForTarget__Stop__state);
                        changeOccurred();
                    }
                }
                break;
            case  1 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #1) priority 1 ----> 
DriveToTarget__StopForTarget__Stop : WAITING (1) -> FINISHED
<ANCESTOR_EXITS_DISJOINED T?> (false || false || <root node's ancestor exit condition>)
[ Set DriveToTarget__StopForTarget__Stop.WAITING.END ]
[ Set DriveToTarget__StopForTarget__Stop.FINISHED.START ]
[ Set outcome of Stop to SKIPPED ]
 ----> (State #6)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__StopForTarget__Stop : WAITING (1) -> FINISHED");
                    }
                    DriveToTarget__StopForTarget__Stop__Stop__outcome.setValue(NodeOutcome.SKIPPED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__Stop__Stop__outcome);
                    DriveToTarget__StopForTarget__Stop__state.setNext(6);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__Stop__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #1) priority 3 ----> 
DriveToTarget__StopForTarget__Stop : WAITING (3) -> FINISHED
<ANCESTOR_INVARIANTS_CONJOINED F?> (true && true && true && <root node's ancestor invariant condition>)
[ Set DriveToTarget__StopForTarget__Stop.WAITING.END ]
[ Set DriveToTarget__StopForTarget__Stop.FINISHED.START ]
[ Set outcome of Stop to SKIPPED ]
 ----> (State #6)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__StopForTarget__Stop : WAITING (3) -> FINISHED");
                        }
                        DriveToTarget__StopForTarget__Stop__Stop__outcome.setValue(NodeOutcome.SKIPPED, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTarget__Stop__Stop__outcome);
                        DriveToTarget__StopForTarget__Stop__state.setNext(6);
                        commitAfterMicroStep(DriveToTarget__StopForTarget__Stop__state);
                        changeOccurred();
                    } else {
                        if ((NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTarget__Stop()).isTrue()&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTarget__SetDriveFlag()).isTrue())||(((((NodeState.FINISHED.equalTo(STATE___DriveToTarget__Drive()).isTrue()&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTimeout()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTarget()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakeNavcam()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakePancam()).isTrue())||getInterface().evalAncestorEnd().isTrue())) {
                            /*
(State #1) priority 4 ----> 
DriveToTarget__StopForTarget__Stop : WAITING (4) -> FINISHED
<ANCESTOR_ENDS_DISJOINED T?> (FINISHED == DriveToTarget__StopForTarget__Stop.state && FINISHED == DriveToTarget__StopForTarget__SetDriveFlag.state || FINISHED == DriveToTarget__Drive.state && FINISHED == DriveToTarget__StopForTimeout.state && FINISHED == DriveToTarget__StopForTarget.state && FINISHED == DriveToTarget__TakeNavcam.state && FINISHED == DriveToTarget__TakePancam.state || <root node's ancestor end condition>)
[ Set DriveToTarget__StopForTarget__Stop.WAITING.END ]
[ Set DriveToTarget__StopForTarget__Stop.FINISHED.START ]
[ Set outcome of Stop to SKIPPED ]
 ----> (State #6)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__StopForTarget__Stop : WAITING (4) -> FINISHED");
                            }
                            DriveToTarget__StopForTarget__Stop__Stop__outcome.setValue(NodeOutcome.SKIPPED, 1);
                            commitAfterMicroStep(DriveToTarget__StopForTarget__Stop__Stop__outcome);
                            DriveToTarget__StopForTarget__Stop__state.setNext(6);
                            commitAfterMicroStep(DriveToTarget__StopForTarget__Stop__state);
                            changeOccurred();
                        } else {
                            /*
(State #1) priority 6 ----> 
DriveToTarget__StopForTarget__Stop : WAITING (6) -> EXECUTING
<START_CONDITION T?> (true)
<PRE_CONDITION T?> (true)
[ Set DriveToTarget__StopForTarget__Stop.WAITING.END ]
[ Set DriveToTarget__StopForTarget__Stop.EXECUTING.START ]
 ----> (State #2)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__StopForTarget__Stop : WAITING (6) -> EXECUTING");
                            }
                            getWorld().command(DriveToTarget__StopForTarget__Stop__command_handle, StringValue.get(("rover_stop")));
                            endMacroStep();
                            DriveToTarget__StopForTarget__Stop__state.setNext(2);
                            commitAfterMicroStep(DriveToTarget__StopForTarget__Stop__state);
                            changeOccurred();
                        }
                    }
                }
                break;
            case  2 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #2) priority 1 ----> 
DriveToTarget__StopForTarget__Stop : EXECUTING (1) -> FAILING
<ANCESTOR_EXITS_DISJOINED T?> (false || false || <root node's ancestor exit condition>)
[ Set DriveToTarget__StopForTarget__Stop.EXECUTING.END ]
[ Set DriveToTarget__StopForTarget__Stop.FAILING.START ]
[ Set outcome of Stop to INTERRUPTED, failure type PARENT_EXITED ]
 ----> (State #5)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__StopForTarget__Stop : EXECUTING (1) -> FAILING");
                    }
                    DriveToTarget__StopForTarget__Stop__Stop__outcome.setValue(NodeOutcome.INTERRUPTED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__Stop__Stop__outcome);
                    DriveToTarget__StopForTarget__Stop__Stop__failure.setValue(NodeFailureType.PARENT_EXITED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__Stop__Stop__failure);
                    DriveToTarget__StopForTarget__Stop__state.setNext(5);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__Stop__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #2) priority 3 ----> 
DriveToTarget__StopForTarget__Stop : EXECUTING (3) -> FAILING
<ANCESTOR_INVARIANTS_CONJOINED F?> (true && true && true && <root node's ancestor invariant condition>)
[ Set DriveToTarget__StopForTarget__Stop.EXECUTING.END ]
[ Set DriveToTarget__StopForTarget__Stop.FAILING.START ]
[ Set outcome of Stop to FAILURE, failure type PARENT_FAILED ]
 ----> (State #5)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__StopForTarget__Stop : EXECUTING (3) -> FAILING");
                        }
                        DriveToTarget__StopForTarget__Stop__Stop__outcome.setValue(NodeOutcome.FAILURE, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTarget__Stop__Stop__outcome);
                        DriveToTarget__StopForTarget__Stop__Stop__failure.setValue(NodeFailureType.PARENT_FAILED, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTarget__Stop__Stop__failure);
                        DriveToTarget__StopForTarget__Stop__state.setNext(5);
                        commitAfterMicroStep(DriveToTarget__StopForTarget__Stop__state);
                        changeOccurred();
                    } else {
                        if (BooleanValue.get(DriveToTarget__StopForTarget__Stop__command_handle.getCommandHandle().isKnown()).isTrue()) {
                            /*
(State #2) priority 5 ----> 
DriveToTarget__StopForTarget__Stop : EXECUTING (5) -> FINISHING
<END_CONDITION T?> (isKnown(DriveToTarget__StopForTarget__Stop.command_handle))
[ Set DriveToTarget__StopForTarget__Stop.EXECUTING.END ]
[ Set DriveToTarget__StopForTarget__Stop.FINISHING.START ]
 ----> (State #3)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__StopForTarget__Stop : EXECUTING (5) -> FINISHING");
                            }
                            DriveToTarget__StopForTarget__Stop__state.setNext(3);
                            commitAfterMicroStep(DriveToTarget__StopForTarget__Stop__state);
                            changeOccurred();
                        }
                    }
                }
                break;
            case  3 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #3) priority 1 ----> 
DriveToTarget__StopForTarget__Stop : FINISHING (1) -> FAILING
<ANCESTOR_EXITS_DISJOINED T?> (false || false || <root node's ancestor exit condition>)
[ Set DriveToTarget__StopForTarget__Stop.FINISHING.END ]
[ Set DriveToTarget__StopForTarget__Stop.FAILING.START ]
[ Set outcome of Stop to INTERRUPTED, failure type PARENT_EXITED ]
 ----> (State #5)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__StopForTarget__Stop : FINISHING (1) -> FAILING");
                    }
                    DriveToTarget__StopForTarget__Stop__Stop__outcome.setValue(NodeOutcome.INTERRUPTED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__Stop__Stop__outcome);
                    DriveToTarget__StopForTarget__Stop__Stop__failure.setValue(NodeFailureType.PARENT_EXITED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__Stop__Stop__failure);
                    DriveToTarget__StopForTarget__Stop__state.setNext(5);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__Stop__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #3) priority 3 ----> 
DriveToTarget__StopForTarget__Stop : FINISHING (3) -> FAILING
<ANCESTOR_INVARIANTS_CONJOINED F?> (true && true && true && <root node's ancestor invariant condition>)
[ Set DriveToTarget__StopForTarget__Stop.FINISHING.END ]
[ Set DriveToTarget__StopForTarget__Stop.FAILING.START ]
[ Set outcome of Stop to FAILURE, failure type PARENT_FAILED ]
 ----> (State #5)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__StopForTarget__Stop : FINISHING (3) -> FAILING");
                        }
                        DriveToTarget__StopForTarget__Stop__Stop__outcome.setValue(NodeOutcome.FAILURE, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTarget__Stop__Stop__outcome);
                        DriveToTarget__StopForTarget__Stop__Stop__failure.setValue(NodeFailureType.PARENT_FAILED, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTarget__Stop__Stop__failure);
                        DriveToTarget__StopForTarget__Stop__state.setNext(5);
                        commitAfterMicroStep(DriveToTarget__StopForTarget__Stop__state);
                        changeOccurred();
                    } else {
                        if (BooleanValue.get(DriveToTarget__StopForTarget__Stop__command_handle.getCommandHandle().isKnown()).isTrue()) {
                            /*
(State #3) priority 5 ----> 
DriveToTarget__StopForTarget__Stop : FINISHING (5) -> ITERATION_ENDED
<COMMAND_ACCEPTED T?> (isKnown(DriveToTarget__StopForTarget__Stop.command_handle))
<POST_CONDITION T?> (true)
[ Set DriveToTarget__StopForTarget__Stop.FINISHING.END ]
[ Set DriveToTarget__StopForTarget__Stop.ITERATION_ENDED.START ]
[ Set outcome of Stop to SUCCESS ]
 ----> (State #4)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__StopForTarget__Stop : FINISHING (5) -> ITERATION_ENDED");
                            }
                            DriveToTarget__StopForTarget__Stop__Stop__outcome.setValue(NodeOutcome.SUCCESS, 1);
                            commitAfterMicroStep(DriveToTarget__StopForTarget__Stop__Stop__outcome);
                            DriveToTarget__StopForTarget__Stop__state.setNext(4);
                            commitAfterMicroStep(DriveToTarget__StopForTarget__Stop__state);
                            changeOccurred();
                        }
                    }
                }
                break;
            case  4 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #4) priority 1 ----> 
DriveToTarget__StopForTarget__Stop : ITERATION_ENDED (1) -> FINISHED
<ANCESTOR_EXITS_DISJOINED T?> (false || false || <root node's ancestor exit condition>)
[ Set DriveToTarget__StopForTarget__Stop.ITERATION_ENDED.END ]
[ Set DriveToTarget__StopForTarget__Stop.FINISHED.START ]
[ Set outcome of Stop to INTERRUPTED, failure type PARENT_EXITED ]
 ----> (State #6)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__StopForTarget__Stop : ITERATION_ENDED (1) -> FINISHED");
                    }
                    DriveToTarget__StopForTarget__Stop__Stop__outcome.setValue(NodeOutcome.INTERRUPTED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__Stop__Stop__outcome);
                    DriveToTarget__StopForTarget__Stop__Stop__failure.setValue(NodeFailureType.PARENT_EXITED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__Stop__Stop__failure);
                    DriveToTarget__StopForTarget__Stop__state.setNext(6);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__Stop__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #4) priority 2 ----> 
DriveToTarget__StopForTarget__Stop : ITERATION_ENDED (2) -> FINISHED
<ANCESTOR_INVARIANTS_CONJOINED F?> (true && true && true && <root node's ancestor invariant condition>)
[ Set DriveToTarget__StopForTarget__Stop.ITERATION_ENDED.END ]
[ Set DriveToTarget__StopForTarget__Stop.FINISHED.START ]
[ Set outcome of Stop to FAILURE, failure type PARENT_FAILED ]
 ----> (State #6)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__StopForTarget__Stop : ITERATION_ENDED (2) -> FINISHED");
                        }
                        DriveToTarget__StopForTarget__Stop__Stop__outcome.setValue(NodeOutcome.FAILURE, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTarget__Stop__Stop__outcome);
                        DriveToTarget__StopForTarget__Stop__Stop__failure.setValue(NodeFailureType.PARENT_FAILED, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTarget__Stop__Stop__failure);
                        DriveToTarget__StopForTarget__Stop__state.setNext(6);
                        commitAfterMicroStep(DriveToTarget__StopForTarget__Stop__state);
                        changeOccurred();
                    } else {
                        if ((NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTarget__Stop()).isTrue()&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTarget__SetDriveFlag()).isTrue())||(((((NodeState.FINISHED.equalTo(STATE___DriveToTarget__Drive()).isTrue()&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTimeout()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTarget()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakeNavcam()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakePancam()).isTrue())||getInterface().evalAncestorEnd().isTrue())) {
                            /*
(State #4) priority 3 ----> 
DriveToTarget__StopForTarget__Stop : ITERATION_ENDED (3) -> FINISHED
<ANCESTOR_ENDS_DISJOINED T?> (FINISHED == DriveToTarget__StopForTarget__Stop.state && FINISHED == DriveToTarget__StopForTarget__SetDriveFlag.state || FINISHED == DriveToTarget__Drive.state && FINISHED == DriveToTarget__StopForTimeout.state && FINISHED == DriveToTarget__StopForTarget.state && FINISHED == DriveToTarget__TakeNavcam.state && FINISHED == DriveToTarget__TakePancam.state || <root node's ancestor end condition>)
[ Set DriveToTarget__StopForTarget__Stop.ITERATION_ENDED.END ]
[ Set DriveToTarget__StopForTarget__Stop.FINISHED.START ]
 ----> (State #6)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__StopForTarget__Stop : ITERATION_ENDED (3) -> FINISHED");
                            }
                            DriveToTarget__StopForTarget__Stop__state.setNext(6);
                            commitAfterMicroStep(DriveToTarget__StopForTarget__Stop__state);
                            changeOccurred();
                        } else {
                            /*
(State #4) priority 4 ----> 
DriveToTarget__StopForTarget__Stop : ITERATION_ENDED (4) -> FINISHED
<REPEAT_CONDITION F?> (false)
[ Set DriveToTarget__StopForTarget__Stop.ITERATION_ENDED.END ]
[ Set DriveToTarget__StopForTarget__Stop.FINISHED.START ]
 ----> (State #6)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__StopForTarget__Stop : ITERATION_ENDED (4) -> FINISHED");
                            }
                            DriveToTarget__StopForTarget__Stop__state.setNext(6);
                            commitAfterMicroStep(DriveToTarget__StopForTarget__Stop__state);
                            changeOccurred();
                        }
                    }
                }
                break;
            case  6 :
                if (STATE___DriveToTarget__StopForTarget().equalTo(NodeState.WAITING).isTrue()) {
                    /*
(State #6) priority 1 ----> 
DriveToTarget__StopForTarget__Stop : FINISHED (1) -> INACTIVE
<PARENT_WAITING T?> (DriveToTarget__StopForTarget.state == WAITING)
[ Set DriveToTarget__StopForTarget__Stop.FINISHED.END ]
[ Set DriveToTarget__StopForTarget__Stop.INACTIVE.START ]
[ Reset variables: DriveToTarget__StopForTarget__Stop.EXECUTING.END, DriveToTarget__StopForTarget__Stop.ITERATION_ENDED.START, Stop.outcome (DriveToTarget__StopForTarget__Stop), DriveToTarget__StopForTarget__Stop.INACTIVE.END, DriveToTarget__StopForTarget__Stop.FAILING.END, DriveToTarget__StopForTarget__Stop.WAITING.START, DriveToTarget__StopForTarget__Stop.EXECUTING.START, DriveToTarget__StopForTarget__Stop.command_handle, DriveToTarget__StopForTarget__Stop.FAILING.START, DriveToTarget__StopForTarget__Stop.INACTIVE.START, DriveToTarget__StopForTarget__Stop.state, DriveToTarget__StopForTarget__Stop.ITERATION_ENDED.END, DriveToTarget__StopForTarget__Stop.FINISHING.END, DriveToTarget__StopForTarget__Stop.FINISHED.END, Stop.failure (DriveToTarget__StopForTarget__Stop), DriveToTarget__StopForTarget__Stop.FINISHING.START, DriveToTarget__StopForTarget__Stop.FINISHED.START, DriveToTarget__StopForTarget__Stop.WAITING.END, ]
 ----> (State #0)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__StopForTarget__Stop : FINISHED (1) -> INACTIVE");
                    }
                    DriveToTarget__StopForTarget__Stop__Stop__outcome.reset();
                    commitAfterMicroStep(DriveToTarget__StopForTarget__Stop__Stop__outcome);
                    DriveToTarget__StopForTarget__Stop__command_handle.reset();
                    DriveToTarget__StopForTarget__Stop__Stop__failure.reset();
                    commitAfterMicroStep(DriveToTarget__StopForTarget__Stop__Stop__failure);
                    DriveToTarget__StopForTarget__Stop__state.setNext(0);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__Stop__state);
                    changeOccurred();
                }
                break;
        }
        /* In Actions executed here: */
        switch (DriveToTarget__StopForTarget__Stop__state.getNext()) {
        }
    }

    public NodeState STATE___DriveToTarget__StopForTarget__Stop() {
        switch (DriveToTarget__StopForTarget__Stop__state.getCurrent()) {
            case  3 :
                return NodeState.FINISHING;
            case  4 :
                return NodeState.ITERATION_ENDED;
            case  2 :
                return NodeState.EXECUTING;
            case  5 :
                return NodeState.FAILING;
            case  1 :
                return NodeState.WAITING;
            case  6 :
                return NodeState.FINISHED;
            case  0 :
                return NodeState.INACTIVE;
        }
        throw new RuntimeException("No state mapping found for DriveToTarget__StopForTarget__Stop");
    }

    void MicroStep___DriveToTarget__StopForTarget__SetDriveFlag() {
        PBoolean temp;
        switch (DriveToTarget__StopForTarget__SetDriveFlag__state.getCurrent()) {
            case  0 :
                if (STATE___DriveToTarget__StopForTarget().equalTo(NodeState.FINISHED).isTrue()) {
                    /*
(State #0) priority 1 ----> 
DriveToTarget__StopForTarget__SetDriveFlag : INACTIVE (1) -> FINISHED
<PARENT_FINISHED T?> (DriveToTarget__StopForTarget.state == FINISHED)
[ Set DriveToTarget__StopForTarget__SetDriveFlag.INACTIVE.END ]
[ Set DriveToTarget__StopForTarget__SetDriveFlag.FINISHED.START ]
[ Set outcome of SetDriveFlag to SKIPPED ]
 ----> (State #6)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__StopForTarget__SetDriveFlag : INACTIVE (1) -> FINISHED");
                    }
                    DriveToTarget__StopForTarget__SetDriveFlag__SetDriveFlag__outcome.setValue(NodeOutcome.SKIPPED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__SetDriveFlag__SetDriveFlag__outcome);
                    DriveToTarget__StopForTarget__SetDriveFlag__state.setNext(6);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__SetDriveFlag__state);
                    changeOccurred();
                } else {
                    if (STATE___DriveToTarget__StopForTarget().equalTo(NodeState.EXECUTING).isTrue()) {
                        /*
(State #0) priority 1 ----> 
DriveToTarget__StopForTarget__SetDriveFlag : INACTIVE (1) -> WAITING
<PARENT_EXECUTING T?> (DriveToTarget__StopForTarget.state == EXECUTING)
[ Set DriveToTarget__StopForTarget__SetDriveFlag.INACTIVE.END ]
[ Set DriveToTarget__StopForTarget__SetDriveFlag.WAITING.START ]
 ----> (State #1)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__StopForTarget__SetDriveFlag : INACTIVE (1) -> WAITING");
                        }
                        DriveToTarget__StopForTarget__SetDriveFlag__state.setNext(1);
                        commitAfterMicroStep(DriveToTarget__StopForTarget__SetDriveFlag__state);
                        changeOccurred();
                    }
                }
                break;
            case  1 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #1) priority 1 ----> 
DriveToTarget__StopForTarget__SetDriveFlag : WAITING (1) -> FINISHED
<ANCESTOR_EXITS_DISJOINED T?> (false || false || <root node's ancestor exit condition>)
[ Set DriveToTarget__StopForTarget__SetDriveFlag.WAITING.END ]
[ Set DriveToTarget__StopForTarget__SetDriveFlag.FINISHED.START ]
[ Set outcome of SetDriveFlag to SKIPPED ]
 ----> (State #6)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__StopForTarget__SetDriveFlag : WAITING (1) -> FINISHED");
                    }
                    DriveToTarget__StopForTarget__SetDriveFlag__SetDriveFlag__outcome.setValue(NodeOutcome.SKIPPED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__SetDriveFlag__SetDriveFlag__outcome);
                    DriveToTarget__StopForTarget__SetDriveFlag__state.setNext(6);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__SetDriveFlag__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #1) priority 3 ----> 
DriveToTarget__StopForTarget__SetDriveFlag : WAITING (3) -> FINISHED
<ANCESTOR_INVARIANTS_CONJOINED F?> (true && true && true && <root node's ancestor invariant condition>)
[ Set DriveToTarget__StopForTarget__SetDriveFlag.WAITING.END ]
[ Set DriveToTarget__StopForTarget__SetDriveFlag.FINISHED.START ]
[ Set outcome of SetDriveFlag to SKIPPED ]
 ----> (State #6)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__StopForTarget__SetDriveFlag : WAITING (3) -> FINISHED");
                        }
                        DriveToTarget__StopForTarget__SetDriveFlag__SetDriveFlag__outcome.setValue(NodeOutcome.SKIPPED, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTarget__SetDriveFlag__SetDriveFlag__outcome);
                        DriveToTarget__StopForTarget__SetDriveFlag__state.setNext(6);
                        commitAfterMicroStep(DriveToTarget__StopForTarget__SetDriveFlag__state);
                        changeOccurred();
                    } else {
                        if ((NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTarget__Stop()).isTrue()&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTarget__SetDriveFlag()).isTrue())||(((((NodeState.FINISHED.equalTo(STATE___DriveToTarget__Drive()).isTrue()&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTimeout()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTarget()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakeNavcam()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakePancam()).isTrue())||getInterface().evalAncestorEnd().isTrue())) {
                            /*
(State #1) priority 4 ----> 
DriveToTarget__StopForTarget__SetDriveFlag : WAITING (4) -> FINISHED
<ANCESTOR_ENDS_DISJOINED T?> (FINISHED == DriveToTarget__StopForTarget__Stop.state && FINISHED == DriveToTarget__StopForTarget__SetDriveFlag.state || FINISHED == DriveToTarget__Drive.state && FINISHED == DriveToTarget__StopForTimeout.state && FINISHED == DriveToTarget__StopForTarget.state && FINISHED == DriveToTarget__TakeNavcam.state && FINISHED == DriveToTarget__TakePancam.state || <root node's ancestor end condition>)
[ Set DriveToTarget__StopForTarget__SetDriveFlag.WAITING.END ]
[ Set DriveToTarget__StopForTarget__SetDriveFlag.FINISHED.START ]
[ Set outcome of SetDriveFlag to SKIPPED ]
 ----> (State #6)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__StopForTarget__SetDriveFlag : WAITING (4) -> FINISHED");
                            }
                            DriveToTarget__StopForTarget__SetDriveFlag__SetDriveFlag__outcome.setValue(NodeOutcome.SKIPPED, 1);
                            commitAfterMicroStep(DriveToTarget__StopForTarget__SetDriveFlag__SetDriveFlag__outcome);
                            DriveToTarget__StopForTarget__SetDriveFlag__state.setNext(6);
                            commitAfterMicroStep(DriveToTarget__StopForTarget__SetDriveFlag__state);
                            changeOccurred();
                        } else {
                            /*
(State #1) priority 6 ----> 
DriveToTarget__StopForTarget__SetDriveFlag : WAITING (6) -> EXECUTING
<START_CONDITION T?> (true)
<PRE_CONDITION T?> (true)
[ Set DriveToTarget__StopForTarget__SetDriveFlag.WAITING.END ]
[ Set DriveToTarget__StopForTarget__SetDriveFlag.EXECUTING.START ]
 ----> (State #2)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__StopForTarget__SetDriveFlag : WAITING (6) -> EXECUTING");
                            }
                            DriveToTarget__drive_done.setValue(BooleanValue.get((true)), 2147483647);
                            commitAfterMacroStep(DriveToTarget__drive_done);
                            endMacroStep();
                            PREV_VALUE___DriveToTarget__StopForTarget__SetDriveFlag = DriveToTarget__drive_done.getValue();
                            DriveToTarget__StopForTarget__SetDriveFlag__state.setNext(2);
                            commitAfterMicroStep(DriveToTarget__StopForTarget__SetDriveFlag__state);
                            changeOccurred();
                        }
                    }
                }
                break;
            case  2 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #2) priority 1 ----> 
DriveToTarget__StopForTarget__SetDriveFlag : EXECUTING (1) -> FAILING
<ANCESTOR_EXITS_DISJOINED T?> (false || false || <root node's ancestor exit condition>)
[ Set DriveToTarget__StopForTarget__SetDriveFlag.EXECUTING.END ]
[ Set DriveToTarget__StopForTarget__SetDriveFlag.FAILING.START ]
[ Set outcome of SetDriveFlag to INTERRUPTED, failure type PARENT_EXITED ]
 ----> (State #5)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__StopForTarget__SetDriveFlag : EXECUTING (1) -> FAILING");
                    }
                    DriveToTarget__StopForTarget__SetDriveFlag__SetDriveFlag__outcome.setValue(NodeOutcome.INTERRUPTED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__SetDriveFlag__SetDriveFlag__outcome);
                    DriveToTarget__StopForTarget__SetDriveFlag__SetDriveFlag__failure.setValue(NodeFailureType.PARENT_EXITED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__SetDriveFlag__SetDriveFlag__failure);
                    DriveToTarget__drive_done.setValue(PREV_VALUE___DriveToTarget__StopForTarget__SetDriveFlag, 2147483647);
                    commitAfterMacroStep(DriveToTarget__drive_done);
                    endMacroStep();
                    DriveToTarget__StopForTarget__SetDriveFlag__state.setNext(5);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__SetDriveFlag__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #2) priority 3 ----> 
DriveToTarget__StopForTarget__SetDriveFlag : EXECUTING (3) -> FAILING
<ANCESTOR_INVARIANTS_CONJOINED F?> (true && true && true && <root node's ancestor invariant condition>)
[ Set DriveToTarget__StopForTarget__SetDriveFlag.EXECUTING.END ]
[ Set DriveToTarget__StopForTarget__SetDriveFlag.FAILING.START ]
[ Set outcome of SetDriveFlag to FAILURE, failure type PARENT_FAILED ]
 ----> (State #5)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__StopForTarget__SetDriveFlag : EXECUTING (3) -> FAILING");
                        }
                        DriveToTarget__StopForTarget__SetDriveFlag__SetDriveFlag__outcome.setValue(NodeOutcome.FAILURE, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTarget__SetDriveFlag__SetDriveFlag__outcome);
                        DriveToTarget__StopForTarget__SetDriveFlag__SetDriveFlag__failure.setValue(NodeFailureType.PARENT_FAILED, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTarget__SetDriveFlag__SetDriveFlag__failure);
                        DriveToTarget__drive_done.setValue(PREV_VALUE___DriveToTarget__StopForTarget__SetDriveFlag, 2147483647);
                        commitAfterMacroStep(DriveToTarget__drive_done);
                        endMacroStep();
                        DriveToTarget__StopForTarget__SetDriveFlag__state.setNext(5);
                        commitAfterMicroStep(DriveToTarget__StopForTarget__SetDriveFlag__state);
                        changeOccurred();
                    } else {
                        /*
(State #2) priority 5 ----> 
DriveToTarget__StopForTarget__SetDriveFlag : EXECUTING (5) -> ITERATION_ENDED
<END_CONDITION T?> (true)
<POST_CONDITION T?> (true)
[ Set DriveToTarget__StopForTarget__SetDriveFlag.EXECUTING.END ]
[ Set DriveToTarget__StopForTarget__SetDriveFlag.ITERATION_ENDED.START ]
[ Set outcome of SetDriveFlag to SUCCESS ]
 ----> (State #4)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__StopForTarget__SetDriveFlag : EXECUTING (5) -> ITERATION_ENDED");
                        }
                        DriveToTarget__StopForTarget__SetDriveFlag__SetDriveFlag__outcome.setValue(NodeOutcome.SUCCESS, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTarget__SetDriveFlag__SetDriveFlag__outcome);
                        DriveToTarget__StopForTarget__SetDriveFlag__state.setNext(4);
                        commitAfterMicroStep(DriveToTarget__StopForTarget__SetDriveFlag__state);
                        changeOccurred();
                    }
                }
                break;
            case  4 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #4) priority 1 ----> 
DriveToTarget__StopForTarget__SetDriveFlag : ITERATION_ENDED (1) -> FINISHED
<ANCESTOR_EXITS_DISJOINED T?> (false || false || <root node's ancestor exit condition>)
[ Set DriveToTarget__StopForTarget__SetDriveFlag.ITERATION_ENDED.END ]
[ Set DriveToTarget__StopForTarget__SetDriveFlag.FINISHED.START ]
[ Set outcome of SetDriveFlag to INTERRUPTED, failure type PARENT_EXITED ]
 ----> (State #6)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__StopForTarget__SetDriveFlag : ITERATION_ENDED (1) -> FINISHED");
                    }
                    DriveToTarget__StopForTarget__SetDriveFlag__SetDriveFlag__outcome.setValue(NodeOutcome.INTERRUPTED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__SetDriveFlag__SetDriveFlag__outcome);
                    DriveToTarget__StopForTarget__SetDriveFlag__SetDriveFlag__failure.setValue(NodeFailureType.PARENT_EXITED, 1);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__SetDriveFlag__SetDriveFlag__failure);
                    DriveToTarget__StopForTarget__SetDriveFlag__state.setNext(6);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__SetDriveFlag__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #4) priority 2 ----> 
DriveToTarget__StopForTarget__SetDriveFlag : ITERATION_ENDED (2) -> FINISHED
<ANCESTOR_INVARIANTS_CONJOINED F?> (true && true && true && <root node's ancestor invariant condition>)
[ Set DriveToTarget__StopForTarget__SetDriveFlag.ITERATION_ENDED.END ]
[ Set DriveToTarget__StopForTarget__SetDriveFlag.FINISHED.START ]
[ Set outcome of SetDriveFlag to FAILURE, failure type PARENT_FAILED ]
 ----> (State #6)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__StopForTarget__SetDriveFlag : ITERATION_ENDED (2) -> FINISHED");
                        }
                        DriveToTarget__StopForTarget__SetDriveFlag__SetDriveFlag__outcome.setValue(NodeOutcome.FAILURE, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTarget__SetDriveFlag__SetDriveFlag__outcome);
                        DriveToTarget__StopForTarget__SetDriveFlag__SetDriveFlag__failure.setValue(NodeFailureType.PARENT_FAILED, 1);
                        commitAfterMicroStep(DriveToTarget__StopForTarget__SetDriveFlag__SetDriveFlag__failure);
                        DriveToTarget__StopForTarget__SetDriveFlag__state.setNext(6);
                        commitAfterMicroStep(DriveToTarget__StopForTarget__SetDriveFlag__state);
                        changeOccurred();
                    } else {
                        if ((NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTarget__Stop()).isTrue()&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTarget__SetDriveFlag()).isTrue())||(((((NodeState.FINISHED.equalTo(STATE___DriveToTarget__Drive()).isTrue()&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTimeout()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTarget()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakeNavcam()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakePancam()).isTrue())||getInterface().evalAncestorEnd().isTrue())) {
                            /*
(State #4) priority 3 ----> 
DriveToTarget__StopForTarget__SetDriveFlag : ITERATION_ENDED (3) -> FINISHED
<ANCESTOR_ENDS_DISJOINED T?> (FINISHED == DriveToTarget__StopForTarget__Stop.state && FINISHED == DriveToTarget__StopForTarget__SetDriveFlag.state || FINISHED == DriveToTarget__Drive.state && FINISHED == DriveToTarget__StopForTimeout.state && FINISHED == DriveToTarget__StopForTarget.state && FINISHED == DriveToTarget__TakeNavcam.state && FINISHED == DriveToTarget__TakePancam.state || <root node's ancestor end condition>)
[ Set DriveToTarget__StopForTarget__SetDriveFlag.ITERATION_ENDED.END ]
[ Set DriveToTarget__StopForTarget__SetDriveFlag.FINISHED.START ]
 ----> (State #6)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__StopForTarget__SetDriveFlag : ITERATION_ENDED (3) -> FINISHED");
                            }
                            DriveToTarget__StopForTarget__SetDriveFlag__state.setNext(6);
                            commitAfterMicroStep(DriveToTarget__StopForTarget__SetDriveFlag__state);
                            changeOccurred();
                        } else {
                            /*
(State #4) priority 4 ----> 
DriveToTarget__StopForTarget__SetDriveFlag : ITERATION_ENDED (4) -> FINISHED
<REPEAT_CONDITION F?> (false)
[ Set DriveToTarget__StopForTarget__SetDriveFlag.ITERATION_ENDED.END ]
[ Set DriveToTarget__StopForTarget__SetDriveFlag.FINISHED.START ]
 ----> (State #6)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__StopForTarget__SetDriveFlag : ITERATION_ENDED (4) -> FINISHED");
                            }
                            DriveToTarget__StopForTarget__SetDriveFlag__state.setNext(6);
                            commitAfterMicroStep(DriveToTarget__StopForTarget__SetDriveFlag__state);
                            changeOccurred();
                        }
                    }
                }
                break;
            case  6 :
                if (STATE___DriveToTarget__StopForTarget().equalTo(NodeState.WAITING).isTrue()) {
                    /*
(State #6) priority 1 ----> 
DriveToTarget__StopForTarget__SetDriveFlag : FINISHED (1) -> INACTIVE
<PARENT_WAITING T?> (DriveToTarget__StopForTarget.state == WAITING)
[ Set DriveToTarget__StopForTarget__SetDriveFlag.FINISHED.END ]
[ Set DriveToTarget__StopForTarget__SetDriveFlag.INACTIVE.START ]
[ Reset variables: DriveToTarget__StopForTarget__SetDriveFlag.EXECUTING.END, DriveToTarget__StopForTarget__SetDriveFlag.ITERATION_ENDED.START, SetDriveFlag.outcome (DriveToTarget__StopForTarget__SetDriveFlag), DriveToTarget__StopForTarget__SetDriveFlag.INACTIVE.END, DriveToTarget__StopForTarget__SetDriveFlag.FAILING.END, DriveToTarget__StopForTarget__SetDriveFlag.WAITING.START, DriveToTarget__StopForTarget__SetDriveFlag.EXECUTING.START, Previous value of DriveToTarget__StopForTarget__SetDriveFlag, DriveToTarget__StopForTarget__SetDriveFlag.FAILING.START, DriveToTarget__StopForTarget__SetDriveFlag.INACTIVE.START, DriveToTarget__StopForTarget__SetDriveFlag.state, DriveToTarget__StopForTarget__SetDriveFlag.ITERATION_ENDED.END, DriveToTarget__StopForTarget__SetDriveFlag.FINISHING.END, DriveToTarget__StopForTarget__SetDriveFlag.FINISHED.END, SetDriveFlag.failure (DriveToTarget__StopForTarget__SetDriveFlag), DriveToTarget__StopForTarget__SetDriveFlag.FINISHING.START, DriveToTarget__StopForTarget__SetDriveFlag.FINISHED.START, DriveToTarget__StopForTarget__SetDriveFlag.WAITING.END, ]
 ----> (State #0)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__StopForTarget__SetDriveFlag : FINISHED (1) -> INACTIVE");
                    }
                    DriveToTarget__StopForTarget__SetDriveFlag__SetDriveFlag__outcome.reset();
                    commitAfterMicroStep(DriveToTarget__StopForTarget__SetDriveFlag__SetDriveFlag__outcome);
                    PREV_VALUE___DriveToTarget__StopForTarget__SetDriveFlag = null;
                    DriveToTarget__StopForTarget__SetDriveFlag__SetDriveFlag__failure.reset();
                    commitAfterMicroStep(DriveToTarget__StopForTarget__SetDriveFlag__SetDriveFlag__failure);
                    DriveToTarget__StopForTarget__SetDriveFlag__state.setNext(0);
                    commitAfterMicroStep(DriveToTarget__StopForTarget__SetDriveFlag__state);
                    changeOccurred();
                }
                break;
        }
        /* In Actions executed here: */
        switch (DriveToTarget__StopForTarget__SetDriveFlag__state.getNext()) {
        }
    }

    public NodeState STATE___DriveToTarget__StopForTarget__SetDriveFlag() {
        switch (DriveToTarget__StopForTarget__SetDriveFlag__state.getCurrent()) {
            case  3 :
                return NodeState.FINISHING;
            case  4 :
                return NodeState.ITERATION_ENDED;
            case  2 :
                return NodeState.EXECUTING;
            case  5 :
                return NodeState.FAILING;
            case  1 :
                return NodeState.WAITING;
            case  6 :
                return NodeState.FINISHED;
            case  0 :
                return NodeState.INACTIVE;
        }
        throw new RuntimeException("No state mapping found for DriveToTarget__StopForTarget__SetDriveFlag");
    }

    void MicroStep___DriveToTarget__TakeNavcam() {
        PBoolean temp;
        switch (DriveToTarget__TakeNavcam__state.getCurrent()) {
            case  0 :
                if (STATE___DriveToTarget().equalTo(NodeState.FINISHED).isTrue()) {
                    /*
(State #0) priority 1 ----> 
DriveToTarget__TakeNavcam : INACTIVE (1) -> FINISHED
<PARENT_FINISHED T?> (DriveToTarget.state == FINISHED)
[ Set DriveToTarget__TakeNavcam.INACTIVE.END ]
[ Set DriveToTarget__TakeNavcam.FINISHED.START ]
[ Set outcome of TakeNavcam to SKIPPED ]
 ----> (State #6)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__TakeNavcam : INACTIVE (1) -> FINISHED");
                    }
                    DriveToTarget__TakeNavcam__TakeNavcam__outcome.setValue(NodeOutcome.SKIPPED, 1);
                    commitAfterMicroStep(DriveToTarget__TakeNavcam__TakeNavcam__outcome);
                    DriveToTarget__TakeNavcam__state.setNext(6);
                    commitAfterMicroStep(DriveToTarget__TakeNavcam__state);
                    changeOccurred();
                } else {
                    if (STATE___DriveToTarget().equalTo(NodeState.EXECUTING).isTrue()) {
                        /*
(State #0) priority 1 ----> 
DriveToTarget__TakeNavcam : INACTIVE (1) -> WAITING
<PARENT_EXECUTING T?> (DriveToTarget.state == EXECUTING)
[ Set DriveToTarget__TakeNavcam.INACTIVE.END ]
[ Set DriveToTarget__TakeNavcam.WAITING.START ]
 ----> (State #1)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__TakeNavcam : INACTIVE (1) -> WAITING");
                        }
                        DriveToTarget__TakeNavcam__state.setNext(1);
                        commitAfterMicroStep(DriveToTarget__TakeNavcam__state);
                        changeOccurred();
                    }
                }
                break;
            case  1 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #1) priority 1 ----> 
DriveToTarget__TakeNavcam : WAITING (1) -> FINISHED
<ANCESTOR_EXITS_DISJOINED T?> (false || <root node's ancestor exit condition>)
[ Set DriveToTarget__TakeNavcam.WAITING.END ]
[ Set DriveToTarget__TakeNavcam.FINISHED.START ]
[ Set outcome of TakeNavcam to SKIPPED ]
 ----> (State #6)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__TakeNavcam : WAITING (1) -> FINISHED");
                    }
                    DriveToTarget__TakeNavcam__TakeNavcam__outcome.setValue(NodeOutcome.SKIPPED, 1);
                    commitAfterMicroStep(DriveToTarget__TakeNavcam__TakeNavcam__outcome);
                    DriveToTarget__TakeNavcam__state.setNext(6);
                    commitAfterMicroStep(DriveToTarget__TakeNavcam__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #1) priority 3 ----> 
DriveToTarget__TakeNavcam : WAITING (3) -> FINISHED
<ANCESTOR_INVARIANTS_CONJOINED F?> (true && true && <root node's ancestor invariant condition>)
[ Set DriveToTarget__TakeNavcam.WAITING.END ]
[ Set DriveToTarget__TakeNavcam.FINISHED.START ]
[ Set outcome of TakeNavcam to SKIPPED ]
 ----> (State #6)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__TakeNavcam : WAITING (3) -> FINISHED");
                        }
                        DriveToTarget__TakeNavcam__TakeNavcam__outcome.setValue(NodeOutcome.SKIPPED, 1);
                        commitAfterMicroStep(DriveToTarget__TakeNavcam__TakeNavcam__outcome);
                        DriveToTarget__TakeNavcam__state.setNext(6);
                        commitAfterMicroStep(DriveToTarget__TakeNavcam__state);
                        changeOccurred();
                    } else {
                        if (((((NodeState.FINISHED.equalTo(STATE___DriveToTarget__Drive()).isTrue()&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTimeout()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTarget()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakeNavcam()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakePancam()).isTrue())||getInterface().evalAncestorEnd().isTrue()) {
                            /*
(State #1) priority 4 ----> 
DriveToTarget__TakeNavcam : WAITING (4) -> FINISHED
<ANCESTOR_ENDS_DISJOINED T?> (FINISHED == DriveToTarget__Drive.state && FINISHED == DriveToTarget__StopForTimeout.state && FINISHED == DriveToTarget__StopForTarget.state && FINISHED == DriveToTarget__TakeNavcam.state && FINISHED == DriveToTarget__TakePancam.state || <root node's ancestor end condition>)
[ Set DriveToTarget__TakeNavcam.WAITING.END ]
[ Set DriveToTarget__TakeNavcam.FINISHED.START ]
[ Set outcome of TakeNavcam to SKIPPED ]
 ----> (State #6)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__TakeNavcam : WAITING (4) -> FINISHED");
                            }
                            DriveToTarget__TakeNavcam__TakeNavcam__outcome.setValue(NodeOutcome.SKIPPED, 1);
                            commitAfterMicroStep(DriveToTarget__TakeNavcam__TakeNavcam__outcome);
                            DriveToTarget__TakeNavcam__state.setNext(6);
                            commitAfterMicroStep(DriveToTarget__TakeNavcam__state);
                            changeOccurred();
                        } else {
                            if (DriveToTarget__drive_done.getValue().isTrue()) {
                                /*
(State #1) priority 5 ----> 
DriveToTarget__TakeNavcam : WAITING (5) -> FINISHED
<SKIP_CONDITION T?> (drive_done (DriveToTarget))
[ Set DriveToTarget__TakeNavcam.WAITING.END ]
[ Set DriveToTarget__TakeNavcam.FINISHED.START ]
[ Set outcome of TakeNavcam to SKIPPED ]
 ----> (State #6)
*/
                                if (JavaPlan.DEBUG) {
                                    System.out.println("DriveToTarget__TakeNavcam : WAITING (5) -> FINISHED");
                                }
                                DriveToTarget__TakeNavcam__TakeNavcam__outcome.setValue(NodeOutcome.SKIPPED, 1);
                                commitAfterMicroStep(DriveToTarget__TakeNavcam__TakeNavcam__outcome);
                                DriveToTarget__TakeNavcam__state.setNext(6);
                                commitAfterMicroStep(DriveToTarget__TakeNavcam__state);
                                changeOccurred();
                            } else {
                                if (DriveToTarget__timeout.getValue().isTrue()) {
                                    /*
(State #1) priority 6 ----> 
DriveToTarget__TakeNavcam : WAITING (6) -> EXECUTING
<START_CONDITION T?> (timeout (DriveToTarget))
<PRE_CONDITION T?> (true)
[ Set DriveToTarget__TakeNavcam.WAITING.END ]
[ Set DriveToTarget__TakeNavcam.EXECUTING.START ]
 ----> (State #2)
*/
                                    if (JavaPlan.DEBUG) {
                                        System.out.println("DriveToTarget__TakeNavcam : WAITING (6) -> EXECUTING");
                                    }
                                    getWorld().command(DriveToTarget__TakeNavcam__command_handle, StringValue.get(("take_navcam")));
                                    endMacroStep();
                                    DriveToTarget__TakeNavcam__state.setNext(2);
                                    commitAfterMicroStep(DriveToTarget__TakeNavcam__state);
                                    changeOccurred();
                                }
                            }
                        }
                    }
                }
                break;
            case  2 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #2) priority 1 ----> 
DriveToTarget__TakeNavcam : EXECUTING (1) -> FAILING
<ANCESTOR_EXITS_DISJOINED T?> (false || <root node's ancestor exit condition>)
[ Set DriveToTarget__TakeNavcam.EXECUTING.END ]
[ Set DriveToTarget__TakeNavcam.FAILING.START ]
[ Set outcome of TakeNavcam to INTERRUPTED, failure type PARENT_EXITED ]
 ----> (State #5)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__TakeNavcam : EXECUTING (1) -> FAILING");
                    }
                    DriveToTarget__TakeNavcam__TakeNavcam__outcome.setValue(NodeOutcome.INTERRUPTED, 1);
                    commitAfterMicroStep(DriveToTarget__TakeNavcam__TakeNavcam__outcome);
                    DriveToTarget__TakeNavcam__TakeNavcam__failure.setValue(NodeFailureType.PARENT_EXITED, 1);
                    commitAfterMicroStep(DriveToTarget__TakeNavcam__TakeNavcam__failure);
                    DriveToTarget__TakeNavcam__state.setNext(5);
                    commitAfterMicroStep(DriveToTarget__TakeNavcam__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #2) priority 3 ----> 
DriveToTarget__TakeNavcam : EXECUTING (3) -> FAILING
<ANCESTOR_INVARIANTS_CONJOINED F?> (true && true && <root node's ancestor invariant condition>)
[ Set DriveToTarget__TakeNavcam.EXECUTING.END ]
[ Set DriveToTarget__TakeNavcam.FAILING.START ]
[ Set outcome of TakeNavcam to FAILURE, failure type PARENT_FAILED ]
 ----> (State #5)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__TakeNavcam : EXECUTING (3) -> FAILING");
                        }
                        DriveToTarget__TakeNavcam__TakeNavcam__outcome.setValue(NodeOutcome.FAILURE, 1);
                        commitAfterMicroStep(DriveToTarget__TakeNavcam__TakeNavcam__outcome);
                        DriveToTarget__TakeNavcam__TakeNavcam__failure.setValue(NodeFailureType.PARENT_FAILED, 1);
                        commitAfterMicroStep(DriveToTarget__TakeNavcam__TakeNavcam__failure);
                        DriveToTarget__TakeNavcam__state.setNext(5);
                        commitAfterMicroStep(DriveToTarget__TakeNavcam__state);
                        changeOccurred();
                    } else {
                        if (BooleanValue.get(DriveToTarget__TakeNavcam__command_handle.getCommandHandle().isKnown()).isTrue()) {
                            /*
(State #2) priority 5 ----> 
DriveToTarget__TakeNavcam : EXECUTING (5) -> FINISHING
<END_CONDITION T?> (isKnown(DriveToTarget__TakeNavcam.command_handle))
[ Set DriveToTarget__TakeNavcam.EXECUTING.END ]
[ Set DriveToTarget__TakeNavcam.FINISHING.START ]
 ----> (State #3)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__TakeNavcam : EXECUTING (5) -> FINISHING");
                            }
                            DriveToTarget__TakeNavcam__state.setNext(3);
                            commitAfterMicroStep(DriveToTarget__TakeNavcam__state);
                            changeOccurred();
                        }
                    }
                }
                break;
            case  3 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #3) priority 1 ----> 
DriveToTarget__TakeNavcam : FINISHING (1) -> FAILING
<ANCESTOR_EXITS_DISJOINED T?> (false || <root node's ancestor exit condition>)
[ Set DriveToTarget__TakeNavcam.FINISHING.END ]
[ Set DriveToTarget__TakeNavcam.FAILING.START ]
[ Set outcome of TakeNavcam to INTERRUPTED, failure type PARENT_EXITED ]
 ----> (State #5)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__TakeNavcam : FINISHING (1) -> FAILING");
                    }
                    DriveToTarget__TakeNavcam__TakeNavcam__outcome.setValue(NodeOutcome.INTERRUPTED, 1);
                    commitAfterMicroStep(DriveToTarget__TakeNavcam__TakeNavcam__outcome);
                    DriveToTarget__TakeNavcam__TakeNavcam__failure.setValue(NodeFailureType.PARENT_EXITED, 1);
                    commitAfterMicroStep(DriveToTarget__TakeNavcam__TakeNavcam__failure);
                    DriveToTarget__TakeNavcam__state.setNext(5);
                    commitAfterMicroStep(DriveToTarget__TakeNavcam__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #3) priority 3 ----> 
DriveToTarget__TakeNavcam : FINISHING (3) -> FAILING
<ANCESTOR_INVARIANTS_CONJOINED F?> (true && true && <root node's ancestor invariant condition>)
[ Set DriveToTarget__TakeNavcam.FINISHING.END ]
[ Set DriveToTarget__TakeNavcam.FAILING.START ]
[ Set outcome of TakeNavcam to FAILURE, failure type PARENT_FAILED ]
 ----> (State #5)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__TakeNavcam : FINISHING (3) -> FAILING");
                        }
                        DriveToTarget__TakeNavcam__TakeNavcam__outcome.setValue(NodeOutcome.FAILURE, 1);
                        commitAfterMicroStep(DriveToTarget__TakeNavcam__TakeNavcam__outcome);
                        DriveToTarget__TakeNavcam__TakeNavcam__failure.setValue(NodeFailureType.PARENT_FAILED, 1);
                        commitAfterMicroStep(DriveToTarget__TakeNavcam__TakeNavcam__failure);
                        DriveToTarget__TakeNavcam__state.setNext(5);
                        commitAfterMicroStep(DriveToTarget__TakeNavcam__state);
                        changeOccurred();
                    } else {
                        if (BooleanValue.get(DriveToTarget__TakeNavcam__command_handle.getCommandHandle().isKnown()).isTrue()) {
                            /*
(State #3) priority 5 ----> 
DriveToTarget__TakeNavcam : FINISHING (5) -> ITERATION_ENDED
<COMMAND_ACCEPTED T?> (isKnown(DriveToTarget__TakeNavcam.command_handle))
<POST_CONDITION T?> (true)
[ Set DriveToTarget__TakeNavcam.FINISHING.END ]
[ Set DriveToTarget__TakeNavcam.ITERATION_ENDED.START ]
[ Set outcome of TakeNavcam to SUCCESS ]
 ----> (State #4)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__TakeNavcam : FINISHING (5) -> ITERATION_ENDED");
                            }
                            DriveToTarget__TakeNavcam__TakeNavcam__outcome.setValue(NodeOutcome.SUCCESS, 1);
                            commitAfterMicroStep(DriveToTarget__TakeNavcam__TakeNavcam__outcome);
                            DriveToTarget__TakeNavcam__state.setNext(4);
                            commitAfterMicroStep(DriveToTarget__TakeNavcam__state);
                            changeOccurred();
                        }
                    }
                }
                break;
            case  4 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #4) priority 1 ----> 
DriveToTarget__TakeNavcam : ITERATION_ENDED (1) -> FINISHED
<ANCESTOR_EXITS_DISJOINED T?> (false || <root node's ancestor exit condition>)
[ Set DriveToTarget__TakeNavcam.ITERATION_ENDED.END ]
[ Set DriveToTarget__TakeNavcam.FINISHED.START ]
[ Set outcome of TakeNavcam to INTERRUPTED, failure type PARENT_EXITED ]
 ----> (State #6)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__TakeNavcam : ITERATION_ENDED (1) -> FINISHED");
                    }
                    DriveToTarget__TakeNavcam__TakeNavcam__outcome.setValue(NodeOutcome.INTERRUPTED, 1);
                    commitAfterMicroStep(DriveToTarget__TakeNavcam__TakeNavcam__outcome);
                    DriveToTarget__TakeNavcam__TakeNavcam__failure.setValue(NodeFailureType.PARENT_EXITED, 1);
                    commitAfterMicroStep(DriveToTarget__TakeNavcam__TakeNavcam__failure);
                    DriveToTarget__TakeNavcam__state.setNext(6);
                    commitAfterMicroStep(DriveToTarget__TakeNavcam__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #4) priority 2 ----> 
DriveToTarget__TakeNavcam : ITERATION_ENDED (2) -> FINISHED
<ANCESTOR_INVARIANTS_CONJOINED F?> (true && true && <root node's ancestor invariant condition>)
[ Set DriveToTarget__TakeNavcam.ITERATION_ENDED.END ]
[ Set DriveToTarget__TakeNavcam.FINISHED.START ]
[ Set outcome of TakeNavcam to FAILURE, failure type PARENT_FAILED ]
 ----> (State #6)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__TakeNavcam : ITERATION_ENDED (2) -> FINISHED");
                        }
                        DriveToTarget__TakeNavcam__TakeNavcam__outcome.setValue(NodeOutcome.FAILURE, 1);
                        commitAfterMicroStep(DriveToTarget__TakeNavcam__TakeNavcam__outcome);
                        DriveToTarget__TakeNavcam__TakeNavcam__failure.setValue(NodeFailureType.PARENT_FAILED, 1);
                        commitAfterMicroStep(DriveToTarget__TakeNavcam__TakeNavcam__failure);
                        DriveToTarget__TakeNavcam__state.setNext(6);
                        commitAfterMicroStep(DriveToTarget__TakeNavcam__state);
                        changeOccurred();
                    } else {
                        if (((((NodeState.FINISHED.equalTo(STATE___DriveToTarget__Drive()).isTrue()&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTimeout()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTarget()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakeNavcam()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakePancam()).isTrue())||getInterface().evalAncestorEnd().isTrue()) {
                            /*
(State #4) priority 3 ----> 
DriveToTarget__TakeNavcam : ITERATION_ENDED (3) -> FINISHED
<ANCESTOR_ENDS_DISJOINED T?> (FINISHED == DriveToTarget__Drive.state && FINISHED == DriveToTarget__StopForTimeout.state && FINISHED == DriveToTarget__StopForTarget.state && FINISHED == DriveToTarget__TakeNavcam.state && FINISHED == DriveToTarget__TakePancam.state || <root node's ancestor end condition>)
[ Set DriveToTarget__TakeNavcam.ITERATION_ENDED.END ]
[ Set DriveToTarget__TakeNavcam.FINISHED.START ]
 ----> (State #6)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__TakeNavcam : ITERATION_ENDED (3) -> FINISHED");
                            }
                            DriveToTarget__TakeNavcam__state.setNext(6);
                            commitAfterMicroStep(DriveToTarget__TakeNavcam__state);
                            changeOccurred();
                        } else {
                            /*
(State #4) priority 4 ----> 
DriveToTarget__TakeNavcam : ITERATION_ENDED (4) -> FINISHED
<REPEAT_CONDITION F?> (false)
[ Set DriveToTarget__TakeNavcam.ITERATION_ENDED.END ]
[ Set DriveToTarget__TakeNavcam.FINISHED.START ]
 ----> (State #6)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__TakeNavcam : ITERATION_ENDED (4) -> FINISHED");
                            }
                            DriveToTarget__TakeNavcam__state.setNext(6);
                            commitAfterMicroStep(DriveToTarget__TakeNavcam__state);
                            changeOccurred();
                        }
                    }
                }
                break;
            case  6 :
                if (STATE___DriveToTarget().equalTo(NodeState.WAITING).isTrue()) {
                    /*
(State #6) priority 1 ----> 
DriveToTarget__TakeNavcam : FINISHED (1) -> INACTIVE
<PARENT_WAITING T?> (DriveToTarget.state == WAITING)
[ Set DriveToTarget__TakeNavcam.FINISHED.END ]
[ Set DriveToTarget__TakeNavcam.INACTIVE.START ]
[ Reset variables: DriveToTarget__TakeNavcam.EXECUTING.END, DriveToTarget__TakeNavcam.ITERATION_ENDED.START, TakeNavcam.outcome (DriveToTarget__TakeNavcam), DriveToTarget__TakeNavcam.INACTIVE.END, DriveToTarget__TakeNavcam.FAILING.END, DriveToTarget__TakeNavcam.WAITING.START, DriveToTarget__TakeNavcam.EXECUTING.START, DriveToTarget__TakeNavcam.command_handle, DriveToTarget__TakeNavcam.FAILING.START, DriveToTarget__TakeNavcam.INACTIVE.START, DriveToTarget__TakeNavcam.state, DriveToTarget__TakeNavcam.ITERATION_ENDED.END, DriveToTarget__TakeNavcam.FINISHING.END, DriveToTarget__TakeNavcam.FINISHED.END, TakeNavcam.failure (DriveToTarget__TakeNavcam), DriveToTarget__TakeNavcam.FINISHING.START, DriveToTarget__TakeNavcam.FINISHED.START, DriveToTarget__TakeNavcam.WAITING.END, ]
 ----> (State #0)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__TakeNavcam : FINISHED (1) -> INACTIVE");
                    }
                    DriveToTarget__TakeNavcam__TakeNavcam__outcome.reset();
                    commitAfterMicroStep(DriveToTarget__TakeNavcam__TakeNavcam__outcome);
                    DriveToTarget__TakeNavcam__command_handle.reset();
                    DriveToTarget__TakeNavcam__TakeNavcam__failure.reset();
                    commitAfterMicroStep(DriveToTarget__TakeNavcam__TakeNavcam__failure);
                    DriveToTarget__TakeNavcam__state.setNext(0);
                    commitAfterMicroStep(DriveToTarget__TakeNavcam__state);
                    changeOccurred();
                }
                break;
        }
        /* In Actions executed here: */
        switch (DriveToTarget__TakeNavcam__state.getNext()) {
        }
    }

    public NodeState STATE___DriveToTarget__TakeNavcam() {
        switch (DriveToTarget__TakeNavcam__state.getCurrent()) {
            case  3 :
                return NodeState.FINISHING;
            case  4 :
                return NodeState.ITERATION_ENDED;
            case  2 :
                return NodeState.EXECUTING;
            case  5 :
                return NodeState.FAILING;
            case  1 :
                return NodeState.WAITING;
            case  6 :
                return NodeState.FINISHED;
            case  0 :
                return NodeState.INACTIVE;
        }
        throw new RuntimeException("No state mapping found for DriveToTarget__TakeNavcam");
    }

    void MicroStep___DriveToTarget__TakePancam() {
        PBoolean temp;
        switch (DriveToTarget__TakePancam__state.getCurrent()) {
            case  0 :
                if (STATE___DriveToTarget().equalTo(NodeState.FINISHED).isTrue()) {
                    /*
(State #0) priority 1 ----> 
DriveToTarget__TakePancam : INACTIVE (1) -> FINISHED
<PARENT_FINISHED T?> (DriveToTarget.state == FINISHED)
[ Set DriveToTarget__TakePancam.INACTIVE.END ]
[ Set DriveToTarget__TakePancam.FINISHED.START ]
[ Set outcome of TakePancam to SKIPPED ]
 ----> (State #6)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__TakePancam : INACTIVE (1) -> FINISHED");
                    }
                    DriveToTarget__TakePancam__TakePancam__outcome.setValue(NodeOutcome.SKIPPED, 1);
                    commitAfterMicroStep(DriveToTarget__TakePancam__TakePancam__outcome);
                    DriveToTarget__TakePancam__state.setNext(6);
                    commitAfterMicroStep(DriveToTarget__TakePancam__state);
                    changeOccurred();
                } else {
                    if (STATE___DriveToTarget().equalTo(NodeState.EXECUTING).isTrue()) {
                        /*
(State #0) priority 1 ----> 
DriveToTarget__TakePancam : INACTIVE (1) -> WAITING
<PARENT_EXECUTING T?> (DriveToTarget.state == EXECUTING)
[ Set DriveToTarget__TakePancam.INACTIVE.END ]
[ Set DriveToTarget__TakePancam.WAITING.START ]
 ----> (State #1)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__TakePancam : INACTIVE (1) -> WAITING");
                        }
                        DriveToTarget__TakePancam__state.setNext(1);
                        commitAfterMicroStep(DriveToTarget__TakePancam__state);
                        changeOccurred();
                    }
                }
                break;
            case  1 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #1) priority 1 ----> 
DriveToTarget__TakePancam : WAITING (1) -> FINISHED
<ANCESTOR_EXITS_DISJOINED T?> (false || <root node's ancestor exit condition>)
[ Set DriveToTarget__TakePancam.WAITING.END ]
[ Set DriveToTarget__TakePancam.FINISHED.START ]
[ Set outcome of TakePancam to SKIPPED ]
 ----> (State #6)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__TakePancam : WAITING (1) -> FINISHED");
                    }
                    DriveToTarget__TakePancam__TakePancam__outcome.setValue(NodeOutcome.SKIPPED, 1);
                    commitAfterMicroStep(DriveToTarget__TakePancam__TakePancam__outcome);
                    DriveToTarget__TakePancam__state.setNext(6);
                    commitAfterMicroStep(DriveToTarget__TakePancam__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #1) priority 3 ----> 
DriveToTarget__TakePancam : WAITING (3) -> FINISHED
<ANCESTOR_INVARIANTS_CONJOINED F?> (true && true && <root node's ancestor invariant condition>)
[ Set DriveToTarget__TakePancam.WAITING.END ]
[ Set DriveToTarget__TakePancam.FINISHED.START ]
[ Set outcome of TakePancam to SKIPPED ]
 ----> (State #6)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__TakePancam : WAITING (3) -> FINISHED");
                        }
                        DriveToTarget__TakePancam__TakePancam__outcome.setValue(NodeOutcome.SKIPPED, 1);
                        commitAfterMicroStep(DriveToTarget__TakePancam__TakePancam__outcome);
                        DriveToTarget__TakePancam__state.setNext(6);
                        commitAfterMicroStep(DriveToTarget__TakePancam__state);
                        changeOccurred();
                    } else {
                        if (((((NodeState.FINISHED.equalTo(STATE___DriveToTarget__Drive()).isTrue()&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTimeout()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTarget()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakeNavcam()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakePancam()).isTrue())||getInterface().evalAncestorEnd().isTrue()) {
                            /*
(State #1) priority 4 ----> 
DriveToTarget__TakePancam : WAITING (4) -> FINISHED
<ANCESTOR_ENDS_DISJOINED T?> (FINISHED == DriveToTarget__Drive.state && FINISHED == DriveToTarget__StopForTimeout.state && FINISHED == DriveToTarget__StopForTarget.state && FINISHED == DriveToTarget__TakeNavcam.state && FINISHED == DriveToTarget__TakePancam.state || <root node's ancestor end condition>)
[ Set DriveToTarget__TakePancam.WAITING.END ]
[ Set DriveToTarget__TakePancam.FINISHED.START ]
[ Set outcome of TakePancam to SKIPPED ]
 ----> (State #6)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__TakePancam : WAITING (4) -> FINISHED");
                            }
                            DriveToTarget__TakePancam__TakePancam__outcome.setValue(NodeOutcome.SKIPPED, 1);
                            commitAfterMicroStep(DriveToTarget__TakePancam__TakePancam__outcome);
                            DriveToTarget__TakePancam__state.setNext(6);
                            commitAfterMicroStep(DriveToTarget__TakePancam__state);
                            changeOccurred();
                        } else {
                            if (DriveToTarget__timeout.getValue().isTrue()) {
                                /*
(State #1) priority 5 ----> 
DriveToTarget__TakePancam : WAITING (5) -> FINISHED
<SKIP_CONDITION T?> (timeout (DriveToTarget))
[ Set DriveToTarget__TakePancam.WAITING.END ]
[ Set DriveToTarget__TakePancam.FINISHED.START ]
[ Set outcome of TakePancam to SKIPPED ]
 ----> (State #6)
*/
                                if (JavaPlan.DEBUG) {
                                    System.out.println("DriveToTarget__TakePancam : WAITING (5) -> FINISHED");
                                }
                                DriveToTarget__TakePancam__TakePancam__outcome.setValue(NodeOutcome.SKIPPED, 1);
                                commitAfterMicroStep(DriveToTarget__TakePancam__TakePancam__outcome);
                                DriveToTarget__TakePancam__state.setNext(6);
                                commitAfterMicroStep(DriveToTarget__TakePancam__state);
                                changeOccurred();
                            } else {
                                if (DriveToTarget__drive_done.getValue().isTrue()) {
                                    /*
(State #1) priority 6 ----> 
DriveToTarget__TakePancam : WAITING (6) -> EXECUTING
<START_CONDITION T?> (drive_done (DriveToTarget))
<PRE_CONDITION T?> (true)
[ Set DriveToTarget__TakePancam.WAITING.END ]
[ Set DriveToTarget__TakePancam.EXECUTING.START ]
 ----> (State #2)
*/
                                    if (JavaPlan.DEBUG) {
                                        System.out.println("DriveToTarget__TakePancam : WAITING (6) -> EXECUTING");
                                    }
                                    getWorld().command(DriveToTarget__TakePancam__command_handle, StringValue.get(("take_pancam")));
                                    endMacroStep();
                                    DriveToTarget__TakePancam__state.setNext(2);
                                    commitAfterMicroStep(DriveToTarget__TakePancam__state);
                                    changeOccurred();
                                }
                            }
                        }
                    }
                }
                break;
            case  2 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #2) priority 1 ----> 
DriveToTarget__TakePancam : EXECUTING (1) -> FAILING
<ANCESTOR_EXITS_DISJOINED T?> (false || <root node's ancestor exit condition>)
[ Set DriveToTarget__TakePancam.EXECUTING.END ]
[ Set DriveToTarget__TakePancam.FAILING.START ]
[ Set outcome of TakePancam to INTERRUPTED, failure type PARENT_EXITED ]
 ----> (State #5)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__TakePancam : EXECUTING (1) -> FAILING");
                    }
                    DriveToTarget__TakePancam__TakePancam__outcome.setValue(NodeOutcome.INTERRUPTED, 1);
                    commitAfterMicroStep(DriveToTarget__TakePancam__TakePancam__outcome);
                    DriveToTarget__TakePancam__TakePancam__failure.setValue(NodeFailureType.PARENT_EXITED, 1);
                    commitAfterMicroStep(DriveToTarget__TakePancam__TakePancam__failure);
                    DriveToTarget__TakePancam__state.setNext(5);
                    commitAfterMicroStep(DriveToTarget__TakePancam__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #2) priority 3 ----> 
DriveToTarget__TakePancam : EXECUTING (3) -> FAILING
<ANCESTOR_INVARIANTS_CONJOINED F?> (true && true && <root node's ancestor invariant condition>)
[ Set DriveToTarget__TakePancam.EXECUTING.END ]
[ Set DriveToTarget__TakePancam.FAILING.START ]
[ Set outcome of TakePancam to FAILURE, failure type PARENT_FAILED ]
 ----> (State #5)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__TakePancam : EXECUTING (3) -> FAILING");
                        }
                        DriveToTarget__TakePancam__TakePancam__outcome.setValue(NodeOutcome.FAILURE, 1);
                        commitAfterMicroStep(DriveToTarget__TakePancam__TakePancam__outcome);
                        DriveToTarget__TakePancam__TakePancam__failure.setValue(NodeFailureType.PARENT_FAILED, 1);
                        commitAfterMicroStep(DriveToTarget__TakePancam__TakePancam__failure);
                        DriveToTarget__TakePancam__state.setNext(5);
                        commitAfterMicroStep(DriveToTarget__TakePancam__state);
                        changeOccurred();
                    } else {
                        if (BooleanValue.get(DriveToTarget__TakePancam__command_handle.getCommandHandle().isKnown()).isTrue()) {
                            /*
(State #2) priority 5 ----> 
DriveToTarget__TakePancam : EXECUTING (5) -> FINISHING
<END_CONDITION T?> (isKnown(DriveToTarget__TakePancam.command_handle))
[ Set DriveToTarget__TakePancam.EXECUTING.END ]
[ Set DriveToTarget__TakePancam.FINISHING.START ]
 ----> (State #3)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__TakePancam : EXECUTING (5) -> FINISHING");
                            }
                            DriveToTarget__TakePancam__state.setNext(3);
                            commitAfterMicroStep(DriveToTarget__TakePancam__state);
                            changeOccurred();
                        }
                    }
                }
                break;
            case  3 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #3) priority 1 ----> 
DriveToTarget__TakePancam : FINISHING (1) -> FAILING
<ANCESTOR_EXITS_DISJOINED T?> (false || <root node's ancestor exit condition>)
[ Set DriveToTarget__TakePancam.FINISHING.END ]
[ Set DriveToTarget__TakePancam.FAILING.START ]
[ Set outcome of TakePancam to INTERRUPTED, failure type PARENT_EXITED ]
 ----> (State #5)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__TakePancam : FINISHING (1) -> FAILING");
                    }
                    DriveToTarget__TakePancam__TakePancam__outcome.setValue(NodeOutcome.INTERRUPTED, 1);
                    commitAfterMicroStep(DriveToTarget__TakePancam__TakePancam__outcome);
                    DriveToTarget__TakePancam__TakePancam__failure.setValue(NodeFailureType.PARENT_EXITED, 1);
                    commitAfterMicroStep(DriveToTarget__TakePancam__TakePancam__failure);
                    DriveToTarget__TakePancam__state.setNext(5);
                    commitAfterMicroStep(DriveToTarget__TakePancam__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #3) priority 3 ----> 
DriveToTarget__TakePancam : FINISHING (3) -> FAILING
<ANCESTOR_INVARIANTS_CONJOINED F?> (true && true && <root node's ancestor invariant condition>)
[ Set DriveToTarget__TakePancam.FINISHING.END ]
[ Set DriveToTarget__TakePancam.FAILING.START ]
[ Set outcome of TakePancam to FAILURE, failure type PARENT_FAILED ]
 ----> (State #5)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__TakePancam : FINISHING (3) -> FAILING");
                        }
                        DriveToTarget__TakePancam__TakePancam__outcome.setValue(NodeOutcome.FAILURE, 1);
                        commitAfterMicroStep(DriveToTarget__TakePancam__TakePancam__outcome);
                        DriveToTarget__TakePancam__TakePancam__failure.setValue(NodeFailureType.PARENT_FAILED, 1);
                        commitAfterMicroStep(DriveToTarget__TakePancam__TakePancam__failure);
                        DriveToTarget__TakePancam__state.setNext(5);
                        commitAfterMicroStep(DriveToTarget__TakePancam__state);
                        changeOccurred();
                    } else {
                        if (BooleanValue.get(DriveToTarget__TakePancam__command_handle.getCommandHandle().isKnown()).isTrue()) {
                            /*
(State #3) priority 5 ----> 
DriveToTarget__TakePancam : FINISHING (5) -> ITERATION_ENDED
<COMMAND_ACCEPTED T?> (isKnown(DriveToTarget__TakePancam.command_handle))
<POST_CONDITION T?> (true)
[ Set DriveToTarget__TakePancam.FINISHING.END ]
[ Set DriveToTarget__TakePancam.ITERATION_ENDED.START ]
[ Set outcome of TakePancam to SUCCESS ]
 ----> (State #4)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__TakePancam : FINISHING (5) -> ITERATION_ENDED");
                            }
                            DriveToTarget__TakePancam__TakePancam__outcome.setValue(NodeOutcome.SUCCESS, 1);
                            commitAfterMicroStep(DriveToTarget__TakePancam__TakePancam__outcome);
                            DriveToTarget__TakePancam__state.setNext(4);
                            commitAfterMicroStep(DriveToTarget__TakePancam__state);
                            changeOccurred();
                        }
                    }
                }
                break;
            case  4 :
                if (getInterface().evalAncestorExit().isTrue()) {
                    /*
(State #4) priority 1 ----> 
DriveToTarget__TakePancam : ITERATION_ENDED (1) -> FINISHED
<ANCESTOR_EXITS_DISJOINED T?> (false || <root node's ancestor exit condition>)
[ Set DriveToTarget__TakePancam.ITERATION_ENDED.END ]
[ Set DriveToTarget__TakePancam.FINISHED.START ]
[ Set outcome of TakePancam to INTERRUPTED, failure type PARENT_EXITED ]
 ----> (State #6)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__TakePancam : ITERATION_ENDED (1) -> FINISHED");
                    }
                    DriveToTarget__TakePancam__TakePancam__outcome.setValue(NodeOutcome.INTERRUPTED, 1);
                    commitAfterMicroStep(DriveToTarget__TakePancam__TakePancam__outcome);
                    DriveToTarget__TakePancam__TakePancam__failure.setValue(NodeFailureType.PARENT_EXITED, 1);
                    commitAfterMicroStep(DriveToTarget__TakePancam__TakePancam__failure);
                    DriveToTarget__TakePancam__state.setNext(6);
                    commitAfterMicroStep(DriveToTarget__TakePancam__state);
                    changeOccurred();
                } else {
                    if (getInterface().evalAncestorInvariant().isFalse()) {
                        /*
(State #4) priority 2 ----> 
DriveToTarget__TakePancam : ITERATION_ENDED (2) -> FINISHED
<ANCESTOR_INVARIANTS_CONJOINED F?> (true && true && <root node's ancestor invariant condition>)
[ Set DriveToTarget__TakePancam.ITERATION_ENDED.END ]
[ Set DriveToTarget__TakePancam.FINISHED.START ]
[ Set outcome of TakePancam to FAILURE, failure type PARENT_FAILED ]
 ----> (State #6)
*/
                        if (JavaPlan.DEBUG) {
                            System.out.println("DriveToTarget__TakePancam : ITERATION_ENDED (2) -> FINISHED");
                        }
                        DriveToTarget__TakePancam__TakePancam__outcome.setValue(NodeOutcome.FAILURE, 1);
                        commitAfterMicroStep(DriveToTarget__TakePancam__TakePancam__outcome);
                        DriveToTarget__TakePancam__TakePancam__failure.setValue(NodeFailureType.PARENT_FAILED, 1);
                        commitAfterMicroStep(DriveToTarget__TakePancam__TakePancam__failure);
                        DriveToTarget__TakePancam__state.setNext(6);
                        commitAfterMicroStep(DriveToTarget__TakePancam__state);
                        changeOccurred();
                    } else {
                        if (((((NodeState.FINISHED.equalTo(STATE___DriveToTarget__Drive()).isTrue()&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTimeout()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__StopForTarget()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakeNavcam()).isTrue())&&NodeState.FINISHED.equalTo(STATE___DriveToTarget__TakePancam()).isTrue())||getInterface().evalAncestorEnd().isTrue()) {
                            /*
(State #4) priority 3 ----> 
DriveToTarget__TakePancam : ITERATION_ENDED (3) -> FINISHED
<ANCESTOR_ENDS_DISJOINED T?> (FINISHED == DriveToTarget__Drive.state && FINISHED == DriveToTarget__StopForTimeout.state && FINISHED == DriveToTarget__StopForTarget.state && FINISHED == DriveToTarget__TakeNavcam.state && FINISHED == DriveToTarget__TakePancam.state || <root node's ancestor end condition>)
[ Set DriveToTarget__TakePancam.ITERATION_ENDED.END ]
[ Set DriveToTarget__TakePancam.FINISHED.START ]
 ----> (State #6)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__TakePancam : ITERATION_ENDED (3) -> FINISHED");
                            }
                            DriveToTarget__TakePancam__state.setNext(6);
                            commitAfterMicroStep(DriveToTarget__TakePancam__state);
                            changeOccurred();
                        } else {
                            /*
(State #4) priority 4 ----> 
DriveToTarget__TakePancam : ITERATION_ENDED (4) -> FINISHED
<REPEAT_CONDITION F?> (false)
[ Set DriveToTarget__TakePancam.ITERATION_ENDED.END ]
[ Set DriveToTarget__TakePancam.FINISHED.START ]
 ----> (State #6)
*/
                            if (JavaPlan.DEBUG) {
                                System.out.println("DriveToTarget__TakePancam : ITERATION_ENDED (4) -> FINISHED");
                            }
                            DriveToTarget__TakePancam__state.setNext(6);
                            commitAfterMicroStep(DriveToTarget__TakePancam__state);
                            changeOccurred();
                        }
                    }
                }
                break;
            case  6 :
                if (STATE___DriveToTarget().equalTo(NodeState.WAITING).isTrue()) {
                    /*
(State #6) priority 1 ----> 
DriveToTarget__TakePancam : FINISHED (1) -> INACTIVE
<PARENT_WAITING T?> (DriveToTarget.state == WAITING)
[ Set DriveToTarget__TakePancam.FINISHED.END ]
[ Set DriveToTarget__TakePancam.INACTIVE.START ]
[ Reset variables: DriveToTarget__TakePancam.EXECUTING.END, DriveToTarget__TakePancam.ITERATION_ENDED.START, TakePancam.outcome (DriveToTarget__TakePancam), DriveToTarget__TakePancam.INACTIVE.END, DriveToTarget__TakePancam.FAILING.END, DriveToTarget__TakePancam.WAITING.START, DriveToTarget__TakePancam.EXECUTING.START, DriveToTarget__TakePancam.command_handle, DriveToTarget__TakePancam.FAILING.START, DriveToTarget__TakePancam.INACTIVE.START, DriveToTarget__TakePancam.state, DriveToTarget__TakePancam.ITERATION_ENDED.END, DriveToTarget__TakePancam.FINISHING.END, DriveToTarget__TakePancam.FINISHED.END, TakePancam.failure (DriveToTarget__TakePancam), DriveToTarget__TakePancam.FINISHING.START, DriveToTarget__TakePancam.FINISHED.START, DriveToTarget__TakePancam.WAITING.END, ]
 ----> (State #0)
*/
                    if (JavaPlan.DEBUG) {
                        System.out.println("DriveToTarget__TakePancam : FINISHED (1) -> INACTIVE");
                    }
                    DriveToTarget__TakePancam__TakePancam__outcome.reset();
                    commitAfterMicroStep(DriveToTarget__TakePancam__TakePancam__outcome);
                    DriveToTarget__TakePancam__command_handle.reset();
                    DriveToTarget__TakePancam__TakePancam__failure.reset();
                    commitAfterMicroStep(DriveToTarget__TakePancam__TakePancam__failure);
                    DriveToTarget__TakePancam__state.setNext(0);
                    commitAfterMicroStep(DriveToTarget__TakePancam__state);
                    changeOccurred();
                }
                break;
        }
        /* In Actions executed here: */
        switch (DriveToTarget__TakePancam__state.getNext()) {
        }
    }

    public NodeState STATE___DriveToTarget__TakePancam() {
        switch (DriveToTarget__TakePancam__state.getCurrent()) {
            case  3 :
                return NodeState.FINISHING;
            case  4 :
                return NodeState.ITERATION_ENDED;
            case  2 :
                return NodeState.EXECUTING;
            case  5 :
                return NodeState.FAILING;
            case  1 :
                return NodeState.WAITING;
            case  6 :
                return NodeState.FINISHED;
            case  0 :
                return NodeState.INACTIVE;
        }
        throw new RuntimeException("No state mapping found for DriveToTarget__TakePancam");
    }

    public void doMicroStep() {
        MicroStep___DriveToTarget();
    }

    public NodeOutcome getRootNodeOutcome() {
        return DriveToTarget__DriveToTarget__outcome.getValue();
    }

    public NodeState getRootNodeState() {
        return STATE___DriveToTarget();
    }

}
