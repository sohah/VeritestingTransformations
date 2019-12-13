(set-option :produce-models true)
(set-option :produce-unsat-cores true)
(define-fun T ((%init Bool) ($signal$0 Int) ($ignition$0 Bool) ($ok$0 Bool) ($T_node_orig~0.start_bt$0 Bool) ($T_node_orig~0.launch_bt$0 Bool) ($T_node_orig~0.reset_flag$0 Bool) ($T_node_repaired~0.start_bt$0 Bool) ($T_node_repaired~0.launch_bt$0 Bool) ($T_node_repaired~0.reset_flag$0 Bool) ($signal$1 Int) ($ignition$1 Bool) ($ok$1 Bool) ($T_node_orig~0.start_bt$1 Bool) ($T_node_orig~0.launch_bt$1 Bool) ($T_node_orig~0.reset_flag$1 Bool) ($T_node_repaired~0.start_bt$1 Bool) ($T_node_repaired~0.launch_bt$1 Bool) ($T_node_repaired~0.reset_flag$1 Bool)) Bool (and (= $ok$1 (and (and (= $T_node_orig~0.start_bt$1 $T_node_repaired~0.start_bt$1) (= $T_node_orig~0.launch_bt$1 $T_node_repaired~0.launch_bt$1)) (= $T_node_orig~0.reset_flag$1 $T_node_repaired~0.reset_flag$1))) (= $T_node_orig~0.start_bt$1 (ite %init false (ite $T_node_orig~0.reset_flag$0 false (ite (and (and (not $T_node_orig~0.start_bt$0) (not $T_node_orig~0.launch_bt$0)) (= $signal$1 0)) true $T_node_orig~0.start_bt$0)))) (= $T_node_orig~0.launch_bt$1 (ite %init false (ite $T_node_orig~0.reset_flag$0 false (ite (and (and $T_node_orig~0.start_bt$0 (not $T_node_orig~0.launch_bt$0)) (= $signal$1 1)) true $T_node_orig~0.launch_bt$0)))) (= $T_node_orig~0.reset_flag$1 (ite %init false $ignition$0)) (= $T_node_repaired~0.start_bt$1 (ite %init false (ite (ite %init false $T_node_repaired~0.reset_flag$0) false (ite (and (and (not $T_node_repaired~0.start_bt$0) (not $T_node_repaired~0.launch_bt$1)) (= $signal$1 (ite %init 0 0))) true $T_node_repaired~0.start_bt$0)))) (= $T_node_repaired~0.launch_bt$1 (ite %init false (ite $T_node_repaired~0.reset_flag$1 false (ite (and (and $T_node_repaired~0.start_bt$1 (not $T_node_repaired~0.launch_bt$0)) (= $signal$1 (ite %init 1 1))) true $T_node_repaired~0.launch_bt$0)))) (= $T_node_repaired~0.reset_flag$1 (ite %init false (ite %init false $ignition$0)))))
(declare-fun %init () Bool)
(declare-fun $signal$~1 () Int)
(declare-fun $ignition$~1 () Bool)
(declare-fun $ok$~1 () Bool)
(declare-fun $T_node_orig~0.start_bt$~1 () Bool)
(declare-fun $T_node_orig~0.launch_bt$~1 () Bool)
(declare-fun $T_node_orig~0.reset_flag$~1 () Bool)
(declare-fun $T_node_repaired~0.start_bt$~1 () Bool)
(declare-fun $T_node_repaired~0.launch_bt$~1 () Bool)
(declare-fun $T_node_repaired~0.reset_flag$~1 () Bool)
; K = 0
(declare-fun $signal$0 () Int)
(declare-fun $ignition$0 () Bool)
(declare-fun $ok$0 () Bool)
(declare-fun $T_node_orig~0.start_bt$0 () Bool)
(declare-fun $T_node_orig~0.launch_bt$0 () Bool)
(declare-fun $T_node_orig~0.reset_flag$0 () Bool)
(declare-fun $T_node_repaired~0.start_bt$0 () Bool)
(declare-fun $T_node_repaired~0.launch_bt$0 () Bool)
(declare-fun $T_node_repaired~0.reset_flag$0 () Bool)
(assert (T %init $signal$~1 $ignition$~1 $ok$~1 $T_node_orig~0.start_bt$~1 $T_node_orig~0.launch_bt$~1 $T_node_orig~0.reset_flag$~1 $T_node_repaired~0.start_bt$~1 $T_node_repaired~0.launch_bt$~1 $T_node_repaired~0.reset_flag$~1 $signal$0 $ignition$0 $ok$0 $T_node_orig~0.start_bt$0 $T_node_orig~0.launch_bt$0 $T_node_orig~0.reset_flag$0 $T_node_repaired~0.start_bt$0 $T_node_repaired~0.launch_bt$0 $T_node_repaired~0.reset_flag$0))
(assert true)
(declare-fun act1 () Bool)
(assert (=> act1 (not (=> true $ok$0))))
(check-sat act1)
(echo "@DONE")
; Z3: sat
; Z3: @DONE
(get-model)
(echo "@DONE")
; Z3: (model 
; Z3:   (define-fun $T_node_repaired~0.reset_flag$0 () Bool
; Z3:     false)
; Z3:   (define-fun act1 () Bool
; Z3:     true)
; Z3:   (define-fun $T_node_orig~0.start_bt$~1 () Bool
; Z3:     false)
; Z3:   (define-fun $T_node_repaired~0.launch_bt$0 () Bool
; Z3:     true)
; Z3:   (define-fun %init () Bool
; Z3:     false)
; Z3:   (define-fun $T_node_orig~0.launch_bt$0 () Bool
; Z3:     true)
; Z3:   (define-fun $T_node_repaired~0.launch_bt$~1 () Bool
; Z3:     false)
; Z3:   (define-fun $T_node_orig~0.start_bt$0 () Bool
; Z3:     false)
; Z3:   (define-fun $ignition$~1 () Bool
; Z3:     false)
; Z3:   (define-fun $T_node_repaired~0.start_bt$0 () Bool
; Z3:     true)
; Z3:   (define-fun $T_node_repaired~0.start_bt$~1 () Bool
; Z3:     true)
; Z3:   (define-fun $T_node_orig~0.launch_bt$~1 () Bool
; Z3:     true)
; Z3:   (define-fun $signal$0 () Int
; Z3:     1)
; Z3:   (define-fun $T_node_orig~0.reset_flag$~1 () Bool
; Z3:     false)
; Z3:   (define-fun $T_node_repaired~0.reset_flag$~1 () Bool
; Z3:     false)
; Z3:   (define-fun $ok$0 () Bool
; Z3:     false)
; Z3:   (define-fun $T_node_orig~0.reset_flag$0 () Bool
; Z3:     false)
; Z3: )
; Z3: @DONE
; K = 1
(declare-fun $signal$1 () Int)
(declare-fun $ignition$1 () Bool)
(declare-fun $ok$1 () Bool)
(declare-fun $T_node_orig~0.start_bt$1 () Bool)
(declare-fun $T_node_orig~0.launch_bt$1 () Bool)
(declare-fun $T_node_orig~0.reset_flag$1 () Bool)
(declare-fun $T_node_repaired~0.start_bt$1 () Bool)
(declare-fun $T_node_repaired~0.launch_bt$1 () Bool)
(declare-fun $T_node_repaired~0.reset_flag$1 () Bool)
(assert (T false $signal$0 $ignition$0 $ok$0 $T_node_orig~0.start_bt$0 $T_node_orig~0.launch_bt$0 $T_node_orig~0.reset_flag$0 $T_node_repaired~0.start_bt$0 $T_node_repaired~0.launch_bt$0 $T_node_repaired~0.reset_flag$0 $signal$1 $ignition$1 $ok$1 $T_node_orig~0.start_bt$1 $T_node_orig~0.launch_bt$1 $T_node_orig~0.reset_flag$1 $T_node_repaired~0.start_bt$1 $T_node_repaired~0.launch_bt$1 $T_node_repaired~0.reset_flag$1))
(assert true)
