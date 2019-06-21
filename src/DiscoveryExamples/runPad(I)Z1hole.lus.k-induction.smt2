(set-option :produce-models true)
(set-option :produce-unsat-cores true)
(define-fun T ((%init Bool) ($hole_0$0 Bool) ($hole_1$0 Bool) ($hole_2$0 Bool) ($hole_3$0 Bool) ($hole_4$0 Bool) ($hole_5$0 Bool) ($hole_6$0 Bool) ($hole_7$0 Bool) ($hole_8$0 Bool) ($ok$0 Bool) ($sig0$0 Int) ($out0$0 Bool) ($Check_spec~0.ok$0 Bool) ($Check_spec~0.step$0 Int) ($Check_spec~0.stepOK$0 Bool) ($Check_spec~1.ok$0 Bool) ($Check_spec~1.step$0 Int) ($Check_spec~1.stepOK$0 Bool) ($Check_spec~0.T_node~0.ok$0 Bool) ($Check_spec~0.T_node~0.start_bt$0 Bool) ($Check_spec~0.T_node~0.launch_bt$0 Bool) ($Check_spec~0.T_node~0.reset_flag$0 Bool) ($Check_spec~0.T_node~0.p1$0 Bool) ($Check_spec~0.H_discovery~0.out$0 Bool) ($Check_spec~1.T_node~0.ok$0 Bool) ($Check_spec~1.T_node~0.start_bt$0 Bool) ($Check_spec~1.T_node~0.launch_bt$0 Bool) ($Check_spec~1.T_node~0.reset_flag$0 Bool) ($Check_spec~1.T_node~0.p1$0 Bool) ($Check_spec~1.H_discovery~0.out$0 Bool) ($~flatten0$0 Int) ($~flatten1$0 Int) ($~flatten2$0 Bool) ($~flatten3$0 Bool) ($hole_0$1 Bool) ($hole_1$1 Bool) ($hole_2$1 Bool) ($hole_3$1 Bool) ($hole_4$1 Bool) ($hole_5$1 Bool) ($hole_6$1 Bool) ($hole_7$1 Bool) ($hole_8$1 Bool) ($ok$1 Bool) ($sig0$1 Int) ($out0$1 Bool) ($Check_spec~0.ok$1 Bool) ($Check_spec~0.step$1 Int) ($Check_spec~0.stepOK$1 Bool) ($Check_spec~1.ok$1 Bool) ($Check_spec~1.step$1 Int) ($Check_spec~1.stepOK$1 Bool) ($Check_spec~0.T_node~0.ok$1 Bool) ($Check_spec~0.T_node~0.start_bt$1 Bool) ($Check_spec~0.T_node~0.launch_bt$1 Bool) ($Check_spec~0.T_node~0.reset_flag$1 Bool) ($Check_spec~0.T_node~0.p1$1 Bool) ($Check_spec~0.H_discovery~0.out$1 Bool) ($Check_spec~1.T_node~0.ok$1 Bool) ($Check_spec~1.T_node~0.start_bt$1 Bool) ($Check_spec~1.T_node~0.launch_bt$1 Bool) ($Check_spec~1.T_node~0.reset_flag$1 Bool) ($Check_spec~1.T_node~0.p1$1 Bool) ($Check_spec~1.H_discovery~0.out$1 Bool) ($~flatten0$1 Int) ($~flatten1$1 Int) ($~flatten2$1 Bool) ($~flatten3$1 Bool)) Bool (and (= $sig0$1 (ite %init 1 $~flatten1$0)) (= $out0$1 (ite %init false $~flatten3$0)) (= $ok$1 (not (and $Check_spec~0.ok$1 $Check_spec~1.ok$1))) (= $Check_spec~0.step$1 (ite %init 0 (+ 1 $Check_spec~0.step$0))) (= $Check_spec~0.stepOK$1 (ite (<= $Check_spec~0.step$1 3) $Check_spec~0.T_node~0.ok$1 true)) (= $Check_spec~0.ok$1 (and (> $Check_spec~0.step$1 3) $Check_spec~0.H_discovery~0.out$1)) (= $Check_spec~1.step$1 (ite %init 0 (+ 1 $Check_spec~1.step$0))) (= $Check_spec~1.stepOK$1 (ite (<= $Check_spec~1.step$1 0) $Check_spec~1.T_node~0.ok$1 true)) (= $Check_spec~1.ok$1 (and (> $Check_spec~1.step$1 0) $Check_spec~1.H_discovery~0.out$1)) (= $Check_spec~0.T_node~0.start_bt$1 (ite %init $hole_2$1 (ite $Check_spec~0.T_node~0.reset_flag$0 $hole_0$1 (ite (and (and (not $Check_spec~0.T_node~0.start_bt$0) (not $Check_spec~0.T_node~0.launch_bt$0)) (= $sig0$1 0)) $hole_1$1 $Check_spec~0.T_node~0.start_bt$0)))) (= $Check_spec~0.T_node~0.launch_bt$1 (ite %init $hole_5$1 (ite $Check_spec~0.T_node~0.reset_flag$0 $hole_3$1 (ite (and (and $Check_spec~0.T_node~0.start_bt$0 (not $Check_spec~0.T_node~0.launch_bt$0)) (= $sig0$1 1)) $hole_4$1 $Check_spec~0.T_node~0.launch_bt$0)))) (= $Check_spec~0.T_node~0.reset_flag$1 (ite %init $hole_6$1 $out0$0)) (= $Check_spec~0.T_node~0.p1$1 (= $out0$1 (ite %init $hole_7$1 (and (and $Check_spec~0.T_node~0.launch_bt$0 (not $Check_spec~0.T_node~0.reset_flag$1)) (not $Check_spec~0.T_node~0.reset_flag$0))))) (= $Check_spec~0.T_node~0.ok$1 (ite %init $hole_8$1 $Check_spec~0.T_node~0.p1$1)) (= $Check_spec~0.H_discovery~0.out$1 (ite %init $Check_spec~0.stepOK$1 (and $Check_spec~0.stepOK$1 $Check_spec~0.H_discovery~0.out$0))) (= $Check_spec~1.T_node~0.start_bt$1 (ite %init $hole_2$1 (ite $Check_spec~1.T_node~0.reset_flag$0 $hole_0$1 (ite (and (and (not $Check_spec~1.T_node~0.start_bt$0) (not $Check_spec~1.T_node~0.launch_bt$0)) (= 1 0)) $hole_1$1 $Check_spec~1.T_node~0.start_bt$0)))) (= $Check_spec~1.T_node~0.launch_bt$1 (ite %init $hole_5$1 (ite $Check_spec~1.T_node~0.reset_flag$0 $hole_3$1 (ite (and (and $Check_spec~1.T_node~0.start_bt$0 (not $Check_spec~1.T_node~0.launch_bt$0)) (= 1 1)) $hole_4$1 $Check_spec~1.T_node~0.launch_bt$0)))) (= $Check_spec~1.T_node~0.reset_flag$1 (ite %init $hole_6$1 false)) (= $Check_spec~1.T_node~0.p1$1 (= false (ite %init $hole_7$1 (and (and $Check_spec~1.T_node~0.launch_bt$0 (not $Check_spec~1.T_node~0.reset_flag$1)) (not $Check_spec~1.T_node~0.reset_flag$0))))) (= $Check_spec~1.T_node~0.ok$1 (ite %init $hole_8$1 $Check_spec~1.T_node~0.p1$1)) (= $Check_spec~1.H_discovery~0.out$1 (ite %init $Check_spec~1.stepOK$1 (and $Check_spec~1.stepOK$1 $Check_spec~1.H_discovery~0.out$0))) (= $~flatten0$1 (ite %init 1 2)) (= $~flatten1$1 (ite %init 0 $~flatten0$0)) (= $~flatten2$1 (ite %init false true)) (= $~flatten3$1 (ite %init false $~flatten2$0)) (ite %init true (= $hole_0$1 $hole_0$0)) (ite %init true (= $hole_1$1 $hole_1$0)) (ite %init true (= $hole_2$1 $hole_2$0)) (ite %init true (= $hole_3$1 $hole_3$0)) (ite %init true (= $hole_4$1 $hole_4$0)) (ite %init true (= $hole_5$1 $hole_5$0)) (ite %init true (= $hole_6$1 $hole_6$0)) (ite %init true (= $hole_7$1 $hole_7$0)) (ite %init true (= $hole_8$1 $hole_8$0))))
(declare-fun %init () Bool)
(declare-fun $hole_0$~1 () Bool)
(declare-fun $hole_1$~1 () Bool)
(declare-fun $hole_2$~1 () Bool)
(declare-fun $hole_3$~1 () Bool)
(declare-fun $hole_4$~1 () Bool)
(declare-fun $hole_5$~1 () Bool)
(declare-fun $hole_6$~1 () Bool)
(declare-fun $hole_7$~1 () Bool)
(declare-fun $hole_8$~1 () Bool)
(declare-fun $ok$~1 () Bool)
(declare-fun $sig0$~1 () Int)
(declare-fun $out0$~1 () Bool)
(declare-fun $Check_spec~0.ok$~1 () Bool)
(declare-fun $Check_spec~0.step$~1 () Int)
(declare-fun $Check_spec~0.stepOK$~1 () Bool)
(declare-fun $Check_spec~1.ok$~1 () Bool)
(declare-fun $Check_spec~1.step$~1 () Int)
(declare-fun $Check_spec~1.stepOK$~1 () Bool)
(declare-fun $Check_spec~0.T_node~0.ok$~1 () Bool)
(declare-fun $Check_spec~0.T_node~0.start_bt$~1 () Bool)
(declare-fun $Check_spec~0.T_node~0.launch_bt$~1 () Bool)
(declare-fun $Check_spec~0.T_node~0.reset_flag$~1 () Bool)
(declare-fun $Check_spec~0.T_node~0.p1$~1 () Bool)
(declare-fun $Check_spec~0.H_discovery~0.out$~1 () Bool)
(declare-fun $Check_spec~1.T_node~0.ok$~1 () Bool)
(declare-fun $Check_spec~1.T_node~0.start_bt$~1 () Bool)
(declare-fun $Check_spec~1.T_node~0.launch_bt$~1 () Bool)
(declare-fun $Check_spec~1.T_node~0.reset_flag$~1 () Bool)
(declare-fun $Check_spec~1.T_node~0.p1$~1 () Bool)
(declare-fun $Check_spec~1.H_discovery~0.out$~1 () Bool)
(declare-fun $~flatten0$~1 () Int)
(declare-fun $~flatten1$~1 () Int)
(declare-fun $~flatten2$~1 () Bool)
(declare-fun $~flatten3$~1 () Bool)
; K = 0
(declare-fun $hole_0$0 () Bool)
(declare-fun $hole_1$0 () Bool)
(declare-fun $hole_2$0 () Bool)
(declare-fun $hole_3$0 () Bool)
(declare-fun $hole_4$0 () Bool)
(declare-fun $hole_5$0 () Bool)
(declare-fun $hole_6$0 () Bool)
(declare-fun $hole_7$0 () Bool)
(declare-fun $hole_8$0 () Bool)
(declare-fun $ok$0 () Bool)
(declare-fun $sig0$0 () Int)
(declare-fun $out0$0 () Bool)
(declare-fun $Check_spec~0.ok$0 () Bool)
(declare-fun $Check_spec~0.step$0 () Int)
(declare-fun $Check_spec~0.stepOK$0 () Bool)
(declare-fun $Check_spec~1.ok$0 () Bool)
(declare-fun $Check_spec~1.step$0 () Int)
(declare-fun $Check_spec~1.stepOK$0 () Bool)
(declare-fun $Check_spec~0.T_node~0.ok$0 () Bool)
(declare-fun $Check_spec~0.T_node~0.start_bt$0 () Bool)
(declare-fun $Check_spec~0.T_node~0.launch_bt$0 () Bool)
(declare-fun $Check_spec~0.T_node~0.reset_flag$0 () Bool)
(declare-fun $Check_spec~0.T_node~0.p1$0 () Bool)
(declare-fun $Check_spec~0.H_discovery~0.out$0 () Bool)
(declare-fun $Check_spec~1.T_node~0.ok$0 () Bool)
(declare-fun $Check_spec~1.T_node~0.start_bt$0 () Bool)
(declare-fun $Check_spec~1.T_node~0.launch_bt$0 () Bool)
(declare-fun $Check_spec~1.T_node~0.reset_flag$0 () Bool)
(declare-fun $Check_spec~1.T_node~0.p1$0 () Bool)
(declare-fun $Check_spec~1.H_discovery~0.out$0 () Bool)
(declare-fun $~flatten0$0 () Int)
(declare-fun $~flatten1$0 () Int)
(declare-fun $~flatten2$0 () Bool)
(declare-fun $~flatten3$0 () Bool)
(assert (T %init $hole_0$~1 $hole_1$~1 $hole_2$~1 $hole_3$~1 $hole_4$~1 $hole_5$~1 $hole_6$~1 $hole_7$~1 $hole_8$~1 $ok$~1 $sig0$~1 $out0$~1 $Check_spec~0.ok$~1 $Check_spec~0.step$~1 $Check_spec~0.stepOK$~1 $Check_spec~1.ok$~1 $Check_spec~1.step$~1 $Check_spec~1.stepOK$~1 $Check_spec~0.T_node~0.ok$~1 $Check_spec~0.T_node~0.start_bt$~1 $Check_spec~0.T_node~0.launch_bt$~1 $Check_spec~0.T_node~0.reset_flag$~1 $Check_spec~0.T_node~0.p1$~1 $Check_spec~0.H_discovery~0.out$~1 $Check_spec~1.T_node~0.ok$~1 $Check_spec~1.T_node~0.start_bt$~1 $Check_spec~1.T_node~0.launch_bt$~1 $Check_spec~1.T_node~0.reset_flag$~1 $Check_spec~1.T_node~0.p1$~1 $Check_spec~1.H_discovery~0.out$~1 $~flatten0$~1 $~flatten1$~1 $~flatten2$~1 $~flatten3$~1 $hole_0$0 $hole_1$0 $hole_2$0 $hole_3$0 $hole_4$0 $hole_5$0 $hole_6$0 $hole_7$0 $hole_8$0 $ok$0 $sig0$0 $out0$0 $Check_spec~0.ok$0 $Check_spec~0.step$0 $Check_spec~0.stepOK$0 $Check_spec~1.ok$0 $Check_spec~1.step$0 $Check_spec~1.stepOK$0 $Check_spec~0.T_node~0.ok$0 $Check_spec~0.T_node~0.start_bt$0 $Check_spec~0.T_node~0.launch_bt$0 $Check_spec~0.T_node~0.reset_flag$0 $Check_spec~0.T_node~0.p1$0 $Check_spec~0.H_discovery~0.out$0 $Check_spec~1.T_node~0.ok$0 $Check_spec~1.T_node~0.start_bt$0 $Check_spec~1.T_node~0.launch_bt$0 $Check_spec~1.T_node~0.reset_flag$0 $Check_spec~1.T_node~0.p1$0 $Check_spec~1.H_discovery~0.out$0 $~flatten0$0 $~flatten1$0 $~flatten2$0 $~flatten3$0))
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
; Z3:   (define-fun $Check_spec~1.stepOK$0 () Bool
; Z3:     true)
; Z3:   (define-fun $hole_5$~1 () Bool
; Z3:     false)
; Z3:   (define-fun $Check_spec~0.T_node~0.start_bt$0 () Bool
; Z3:     false)
; Z3:   (define-fun $Check_spec~1.ok$0 () Bool
; Z3:     true)
; Z3:   (define-fun $hole_6$0 () Bool
; Z3:     false)
; Z3:   (define-fun $sig0$0 () Int
; Z3:     5)
; Z3:   (define-fun $hole_2$0 () Bool
; Z3:     false)
; Z3:   (define-fun $Check_spec~0.ok$0 () Bool
; Z3:     true)
; Z3:   (define-fun $hole_3$0 () Bool
; Z3:     false)
; Z3:   (define-fun $~flatten1$0 () Int
; Z3:     6)
; Z3:   (define-fun $Check_spec~1.T_node~0.reset_flag$0 () Bool
; Z3:     false)
; Z3:   (define-fun $~flatten2$0 () Bool
; Z3:     true)
; Z3:   (define-fun $Check_spec~0.T_node~0.p1$0 () Bool
; Z3:     false)
; Z3:   (define-fun $~flatten0$0 () Int
; Z3:     2)
; Z3:   (define-fun $hole_1$0 () Bool
; Z3:     false)
; Z3:   (define-fun $~flatten3$~1 () Bool
; Z3:     true)
; Z3:   (define-fun $hole_1$~1 () Bool
; Z3:     false)
; Z3:   (define-fun act1 () Bool
; Z3:     true)
; Z3:   (define-fun $hole_0$0 () Bool
; Z3:     false)
; Z3:   (define-fun $hole_2$~1 () Bool
; Z3:     false)
; Z3:   (define-fun $Check_spec~0.stepOK$0 () Bool
; Z3:     true)
; Z3:   (define-fun $Check_spec~1.step$0 () Int
; Z3:     1)
; Z3:   (define-fun $out0$~1 () Bool
; Z3:     false)
; Z3:   (define-fun $Check_spec~1.T_node~0.launch_bt$~1 () Bool
; Z3:     true)
; Z3:   (define-fun $Check_spec~1.T_node~0.launch_bt$0 () Bool
; Z3:     true)
; Z3:   (define-fun $Check_spec~0.H_discovery~0.out$0 () Bool
; Z3:     true)
; Z3:   (define-fun $hole_7$~1 () Bool
; Z3:     false)
; Z3:   (define-fun $hole_8$~1 () Bool
; Z3:     false)
; Z3:   (define-fun $hole_4$0 () Bool
; Z3:     false)
; Z3:   (define-fun $hole_6$~1 () Bool
; Z3:     false)
; Z3:   (define-fun $hole_5$0 () Bool
; Z3:     false)
; Z3:   (define-fun $hole_0$~1 () Bool
; Z3:     false)
; Z3:   (define-fun $ok$0 () Bool
; Z3:     false)
; Z3:   (define-fun $Check_spec~1.T_node~0.start_bt$~1 () Bool
; Z3:     false)
; Z3:   (define-fun $Check_spec~1.H_discovery~0.out$0 () Bool
; Z3:     true)
; Z3:   (define-fun $~flatten0$~1 () Int
; Z3:     6)
; Z3:   (define-fun $hole_7$0 () Bool
; Z3:     false)
; Z3:   (define-fun $hole_8$0 () Bool
; Z3:     false)
; Z3:   (define-fun $Check_spec~1.T_node~0.p1$0 () Bool
; Z3:     false)
; Z3:   (define-fun $Check_spec~1.T_node~0.reset_flag$~1 () Bool
; Z3:     false)
; Z3:   (define-fun $hole_3$~1 () Bool
; Z3:     false)
; Z3:   (define-fun $Check_spec~0.T_node~0.launch_bt$0 () Bool
; Z3:     false)
; Z3:   (define-fun $~flatten2$~1 () Bool
; Z3:     true)
; Z3:   (define-fun $hole_4$~1 () Bool
; Z3:     false)
; Z3:   (define-fun $Check_spec~1.T_node~0.ok$0 () Bool
; Z3:     false)
; Z3:   (define-fun $Check_spec~0.step$0 () Int
; Z3:     4)
; Z3:   (define-fun $~flatten1$~1 () Int
; Z3:     5)
; Z3:   (define-fun %init () Bool
; Z3:     false)
; Z3:   (define-fun $out0$0 () Bool
; Z3:     true)
; Z3:   (define-fun $Check_spec~0.T_node~0.ok$0 () Bool
; Z3:     false)
; Z3:   (define-fun $Check_spec~0.T_node~0.reset_flag$~1 () Bool
; Z3:     true)
; Z3:   (define-fun $~flatten3$0 () Bool
; Z3:     true)
; Z3:   (define-fun $Check_spec~0.T_node~0.reset_flag$0 () Bool
; Z3:     false)
; Z3:   (define-fun $Check_spec~0.H_discovery~0.out$~1 () Bool
; Z3:     true)
; Z3:   (define-fun $Check_spec~0.step$~1 () Int
; Z3:     3)
; Z3:   (define-fun $Check_spec~1.H_discovery~0.out$~1 () Bool
; Z3:     true)
; Z3:   (define-fun $Check_spec~1.T_node~0.start_bt$0 () Bool
; Z3:     false)
; Z3:   (define-fun $Check_spec~1.step$~1 () Int
; Z3:     0)
; Z3: )
; Z3: @DONE
; K = 1
(declare-fun $hole_0$1 () Bool)
(declare-fun $hole_1$1 () Bool)
(declare-fun $hole_2$1 () Bool)
(declare-fun $hole_3$1 () Bool)
(declare-fun $hole_4$1 () Bool)
(declare-fun $hole_5$1 () Bool)
(declare-fun $hole_6$1 () Bool)
(declare-fun $hole_7$1 () Bool)
(declare-fun $hole_8$1 () Bool)
(declare-fun $ok$1 () Bool)
(declare-fun $sig0$1 () Int)
(declare-fun $out0$1 () Bool)
(declare-fun $Check_spec~0.ok$1 () Bool)
(declare-fun $Check_spec~0.step$1 () Int)
(declare-fun $Check_spec~0.stepOK$1 () Bool)
(declare-fun $Check_spec~1.ok$1 () Bool)
(declare-fun $Check_spec~1.step$1 () Int)
(declare-fun $Check_spec~1.stepOK$1 () Bool)
(declare-fun $Check_spec~0.T_node~0.ok$1 () Bool)
(declare-fun $Check_spec~0.T_node~0.start_bt$1 () Bool)
(declare-fun $Check_spec~0.T_node~0.launch_bt$1 () Bool)
(declare-fun $Check_spec~0.T_node~0.reset_flag$1 () Bool)
(declare-fun $Check_spec~0.T_node~0.p1$1 () Bool)
(declare-fun $Check_spec~0.H_discovery~0.out$1 () Bool)
(declare-fun $Check_spec~1.T_node~0.ok$1 () Bool)
(declare-fun $Check_spec~1.T_node~0.start_bt$1 () Bool)
(declare-fun $Check_spec~1.T_node~0.launch_bt$1 () Bool)
(declare-fun $Check_spec~1.T_node~0.reset_flag$1 () Bool)
(declare-fun $Check_spec~1.T_node~0.p1$1 () Bool)
(declare-fun $Check_spec~1.H_discovery~0.out$1 () Bool)
(declare-fun $~flatten0$1 () Int)
(declare-fun $~flatten1$1 () Int)
(declare-fun $~flatten2$1 () Bool)
(declare-fun $~flatten3$1 () Bool)
(assert (T false $hole_0$0 $hole_1$0 $hole_2$0 $hole_3$0 $hole_4$0 $hole_5$0 $hole_6$0 $hole_7$0 $hole_8$0 $ok$0 $sig0$0 $out0$0 $Check_spec~0.ok$0 $Check_spec~0.step$0 $Check_spec~0.stepOK$0 $Check_spec~1.ok$0 $Check_spec~1.step$0 $Check_spec~1.stepOK$0 $Check_spec~0.T_node~0.ok$0 $Check_spec~0.T_node~0.start_bt$0 $Check_spec~0.T_node~0.launch_bt$0 $Check_spec~0.T_node~0.reset_flag$0 $Check_spec~0.T_node~0.p1$0 $Check_spec~0.H_discovery~0.out$0 $Check_spec~1.T_node~0.ok$0 $Check_spec~1.T_node~0.start_bt$0 $Check_spec~1.T_node~0.launch_bt$0 $Check_spec~1.T_node~0.reset_flag$0 $Check_spec~1.T_node~0.p1$0 $Check_spec~1.H_discovery~0.out$0 $~flatten0$0 $~flatten1$0 $~flatten2$0 $~flatten3$0 $hole_0$1 $hole_1$1 $hole_2$1 $hole_3$1 $hole_4$1 $hole_5$1 $hole_6$1 $hole_7$1 $hole_8$1 $ok$1 $sig0$1 $out0$1 $Check_spec~0.ok$1 $Check_spec~0.step$1 $Check_spec~0.stepOK$1 $Check_spec~1.ok$1 $Check_spec~1.step$1 $Check_spec~1.stepOK$1 $Check_spec~0.T_node~0.ok$1 $Check_spec~0.T_node~0.start_bt$1 $Check_spec~0.T_node~0.launch_bt$1 $Check_spec~0.T_node~0.reset_flag$1 $Check_spec~0.T_node~0.p1$1 $Check_spec~0.H_discovery~0.out$1 $Check_spec~1.T_node~0.ok$1 $Check_spec~1.T_node~0.start_bt$1 $Check_spec~1.T_node~0.launch_bt$1 $Check_spec~1.T_node~0.reset_flag$1 $Check_spec~1.T_node~0.p1$1 $Check_spec~1.H_discovery~0.out$1 $~flatten0$1 $~flatten1$1 $~flatten2$1 $~flatten3$1))
(assert true)
(declare-fun act2 () Bool)
(assert (=> act2 (not (=> $ok$0 $ok$1))))
(check-sat act2)
(echo "@DONE")
; Z3: sat
; Z3: @DONE
(get-model)
(echo "@DONE")
; Z3: (model 
; Z3:   (define-fun $Check_spec~1.stepOK$0 () Bool
; Z3:     true)
; Z3:   (define-fun $hole_5$~1 () Bool
; Z3:     false)
; Z3:   (define-fun $Check_spec~0.T_node~0.start_bt$0 () Bool
; Z3:     true)
; Z3:   (define-fun $hole_7$1 () Bool
; Z3:     false)
; Z3:   (define-fun $Check_spec~1.ok$0 () Bool
; Z3:     true)
; Z3:   (define-fun $hole_6$0 () Bool
; Z3:     false)
; Z3:   (define-fun $sig0$0 () Int
; Z3:     1)
; Z3:   (define-fun $ok$1 () Bool
; Z3:     false)
; Z3:   (define-fun $sig0$1 () Int
; Z3:     1)
; Z3:   (define-fun $hole_2$0 () Bool
; Z3:     false)
; Z3:   (define-fun $Check_spec~0.T_node~0.start_bt$~1 () Bool
; Z3:     true)
; Z3:   (define-fun $Check_spec~0.ok$0 () Bool
; Z3:     false)
; Z3:   (define-fun $hole_2$1 () Bool
; Z3:     false)
; Z3:   (define-fun $hole_3$0 () Bool
; Z3:     false)
; Z3:   (define-fun $Check_spec~0.T_node~0.start_bt$1 () Bool
; Z3:     true)
; Z3:   (define-fun $~flatten1$0 () Int
; Z3:     1)
; Z3:   (define-fun $~flatten0$1 () Int
; Z3:     2)
; Z3:   (define-fun $Check_spec~1.T_node~0.reset_flag$0 () Bool
; Z3:     false)
; Z3:   (define-fun $~flatten2$0 () Bool
; Z3:     true)
; Z3:   (define-fun $Check_spec~0.T_node~0.p1$0 () Bool
; Z3:     true)
; Z3:   (define-fun $hole_4$1 () Bool
; Z3:     false)
; Z3:   (define-fun $hole_6$1 () Bool
; Z3:     false)
; Z3:   (define-fun $~flatten0$0 () Int
; Z3:     2)
; Z3:   (define-fun $hole_1$0 () Bool
; Z3:     false)
; Z3:   (define-fun $Check_spec~1.T_node~0.ok$1 () Bool
; Z3:     false)
; Z3:   (define-fun $~flatten3$~1 () Bool
; Z3:     false)
; Z3:   (define-fun $hole_1$~1 () Bool
; Z3:     false)
; Z3:   (define-fun act1 () Bool
; Z3:     false)
; Z3:   (define-fun $hole_0$0 () Bool
; Z3:     false)
; Z3:   (define-fun $hole_2$~1 () Bool
; Z3:     false)
; Z3:   (define-fun $~flatten3$1 () Bool
; Z3:     true)
; Z3:   (define-fun act2 () Bool
; Z3:     true)
; Z3:   (define-fun $Check_spec~1.ok$1 () Bool
; Z3:     true)
; Z3:   (define-fun $Check_spec~0.stepOK$0 () Bool
; Z3:     true)
; Z3:   (define-fun $Check_spec~1.step$0 () Int
; Z3:     1)
; Z3:   (define-fun $Check_spec~1.T_node~0.start_bt$1 () Bool
; Z3:     false)
; Z3:   (define-fun $out0$~1 () Bool
; Z3:     false)
; Z3:   (define-fun $Check_spec~1.T_node~0.launch_bt$~1 () Bool
; Z3:     true)
; Z3:   (define-fun $Check_spec~1.T_node~0.launch_bt$0 () Bool
; Z3:     true)
; Z3:   (define-fun $Check_spec~1.step$1 () Int
; Z3:     2)
; Z3:   (define-fun $Check_spec~0.H_discovery~0.out$0 () Bool
; Z3:     true)
; Z3:   (define-fun $Check_spec~1.H_discovery~0.out$1 () Bool
; Z3:     true)
; Z3:   (define-fun $hole_7$~1 () Bool
; Z3:     false)
; Z3:   (define-fun $hole_4$0 () Bool
; Z3:     false)
; Z3:   (define-fun $hole_5$0 () Bool
; Z3:     false)
; Z3:   (define-fun $hole_6$~1 () Bool
; Z3:     false)
; Z3:   (define-fun $ok$0 () Bool
; Z3:     true)
; Z3:   (define-fun $hole_0$~1 () Bool
; Z3:     false)
; Z3:   (define-fun $Check_spec~1.T_node~0.start_bt$~1 () Bool
; Z3:     false)
; Z3:   (define-fun $hole_8$~1 () Bool
; Z3:     false)
; Z3:   (define-fun $Check_spec~0.T_node~0.reset_flag$1 () Bool
; Z3:     false)
; Z3:   (define-fun $Check_spec~0.T_node~0.ok$1 () Bool
; Z3:     false)
; Z3:   (define-fun $hole_8$1 () Bool
; Z3:     false)
; Z3:   (define-fun $Check_spec~1.H_discovery~0.out$0 () Bool
; Z3:     true)
; Z3:   (define-fun $Check_spec~0.T_node~0.launch_bt$1 () Bool
; Z3:     false)
; Z3:   (define-fun $hole_1$1 () Bool
; Z3:     false)
; Z3:   (define-fun $hole_7$0 () Bool
; Z3:     false)
; Z3:   (define-fun $~flatten0$~1 () Int
; Z3:     1)
; Z3:   (define-fun $hole_8$0 () Bool
; Z3:     false)
; Z3:   (define-fun $Check_spec~1.T_node~0.p1$0 () Bool
; Z3:     false)
; Z3:   (define-fun $hole_0$1 () Bool
; Z3:     false)
; Z3:   (define-fun $Check_spec~0.T_node~0.launch_bt$~1 () Bool
; Z3:     false)
; Z3:   (define-fun $Check_spec~1.T_node~0.reset_flag$~1 () Bool
; Z3:     false)
; Z3:   (define-fun $hole_3$~1 () Bool
; Z3:     false)
; Z3:   (define-fun $Check_spec~0.T_node~0.launch_bt$0 () Bool
; Z3:     false)
; Z3:   (define-fun $hole_3$1 () Bool
; Z3:     false)
; Z3:   (define-fun $~flatten2$~1 () Bool
; Z3:     true)
; Z3:   (define-fun $hole_4$~1 () Bool
; Z3:     false)
; Z3:   (define-fun $Check_spec~1.T_node~0.ok$0 () Bool
; Z3:     false)
; Z3:   (define-fun $Check_spec~1.stepOK$1 () Bool
; Z3:     true)
; Z3:   (define-fun $~flatten1$~1 () Int
; Z3:     1)
; Z3:   (define-fun %init () Bool
; Z3:     false)
; Z3:   (define-fun $out0$0 () Bool
; Z3:     false)
; Z3:   (define-fun $Check_spec~0.T_node~0.ok$0 () Bool
; Z3:     true)
; Z3:   (define-fun $Check_spec~1.T_node~0.launch_bt$1 () Bool
; Z3:     true)
; Z3:   (define-fun $hole_5$1 () Bool
; Z3:     false)
; Z3:   (define-fun $Check_spec~0.ok$1 () Bool
; Z3:     true)
; Z3:   (define-fun $Check_spec~0.step$0 () Int
; Z3:     3)
; Z3:   (define-fun $Check_spec~0.T_node~0.reset_flag$~1 () Bool
; Z3:     false)
; Z3:   (define-fun $~flatten2$1 () Bool
; Z3:     true)
; Z3:   (define-fun $Check_spec~0.T_node~0.p1$1 () Bool
; Z3:     false)
; Z3:   (define-fun $~flatten3$0 () Bool
; Z3:     true)
; Z3:   (define-fun $Check_spec~0.T_node~0.reset_flag$0 () Bool
; Z3:     false)
; Z3:   (define-fun $Check_spec~0.H_discovery~0.out$~1 () Bool
; Z3:     true)
; Z3:   (define-fun $Check_spec~0.stepOK$1 () Bool
; Z3:     true)
; Z3:   (define-fun $Check_spec~0.H_discovery~0.out$1 () Bool
; Z3:     true)
; Z3:   (define-fun $Check_spec~1.T_node~0.reset_flag$1 () Bool
; Z3:     false)
; Z3:   (define-fun $Check_spec~1.T_node~0.p1$1 () Bool
; Z3:     false)
; Z3:   (define-fun $Check_spec~0.step$~1 () Int
; Z3:     2)
; Z3:   (define-fun $out0$1 () Bool
; Z3:     true)
; Z3:   (define-fun $Check_spec~1.H_discovery~0.out$~1 () Bool
; Z3:     true)
; Z3:   (define-fun $Check_spec~1.T_node~0.start_bt$0 () Bool
; Z3:     false)
; Z3:   (define-fun $Check_spec~1.step$~1 () Int
; Z3:     0)
; Z3:   (define-fun $Check_spec~0.step$1 () Int
; Z3:     4)
; Z3:   (define-fun $~flatten1$1 () Int
; Z3:     2)
; Z3: )
; Z3: @DONE
; K = 2
(declare-fun $hole_0$2 () Bool)
(declare-fun $hole_1$2 () Bool)
(declare-fun $hole_2$2 () Bool)
(declare-fun $hole_3$2 () Bool)
(declare-fun $hole_4$2 () Bool)
(declare-fun $hole_5$2 () Bool)
(declare-fun $hole_6$2 () Bool)
(declare-fun $hole_7$2 () Bool)
(declare-fun $hole_8$2 () Bool)
(declare-fun $ok$2 () Bool)
(declare-fun $sig0$2 () Int)
(declare-fun $out0$2 () Bool)
(declare-fun $Check_spec~0.ok$2 () Bool)
(declare-fun $Check_spec~0.step$2 () Int)
(declare-fun $Check_spec~0.stepOK$2 () Bool)
(declare-fun $Check_spec~1.ok$2 () Bool)
(declare-fun $Check_spec~1.step$2 () Int)
(declare-fun $Check_spec~1.stepOK$2 () Bool)
(declare-fun $Check_spec~0.T_node~0.ok$2 () Bool)
(declare-fun $Check_spec~0.T_node~0.start_bt$2 () Bool)
(declare-fun $Check_spec~0.T_node~0.launch_bt$2 () Bool)
(declare-fun $Check_spec~0.T_node~0.reset_flag$2 () Bool)
(declare-fun $Check_spec~0.T_node~0.p1$2 () Bool)
(declare-fun $Check_spec~0.H_discovery~0.out$2 () Bool)
(declare-fun $Check_spec~1.T_node~0.ok$2 () Bool)
(declare-fun $Check_spec~1.T_node~0.start_bt$2 () Bool)
(declare-fun $Check_spec~1.T_node~0.launch_bt$2 () Bool)
(declare-fun $Check_spec~1.T_node~0.reset_flag$2 () Bool)
(declare-fun $Check_spec~1.T_node~0.p1$2 () Bool)
(declare-fun $Check_spec~1.H_discovery~0.out$2 () Bool)
(declare-fun $~flatten0$2 () Int)
(declare-fun $~flatten1$2 () Int)
(declare-fun $~flatten2$2 () Bool)
(declare-fun $~flatten3$2 () Bool)
(assert (T false $hole_0$1 $hole_1$1 $hole_2$1 $hole_3$1 $hole_4$1 $hole_5$1 $hole_6$1 $hole_7$1 $hole_8$1 $ok$1 $sig0$1 $out0$1 $Check_spec~0.ok$1 $Check_spec~0.step$1 $Check_spec~0.stepOK$1 $Check_spec~1.ok$1 $Check_spec~1.step$1 $Check_spec~1.stepOK$1 $Check_spec~0.T_node~0.ok$1 $Check_spec~0.T_node~0.start_bt$1 $Check_spec~0.T_node~0.launch_bt$1 $Check_spec~0.T_node~0.reset_flag$1 $Check_spec~0.T_node~0.p1$1 $Check_spec~0.H_discovery~0.out$1 $Check_spec~1.T_node~0.ok$1 $Check_spec~1.T_node~0.start_bt$1 $Check_spec~1.T_node~0.launch_bt$1 $Check_spec~1.T_node~0.reset_flag$1 $Check_spec~1.T_node~0.p1$1 $Check_spec~1.H_discovery~0.out$1 $~flatten0$1 $~flatten1$1 $~flatten2$1 $~flatten3$1 $hole_0$2 $hole_1$2 $hole_2$2 $hole_3$2 $hole_4$2 $hole_5$2 $hole_6$2 $hole_7$2 $hole_8$2 $ok$2 $sig0$2 $out0$2 $Check_spec~0.ok$2 $Check_spec~0.step$2 $Check_spec~0.stepOK$2 $Check_spec~1.ok$2 $Check_spec~1.step$2 $Check_spec~1.stepOK$2 $Check_spec~0.T_node~0.ok$2 $Check_spec~0.T_node~0.start_bt$2 $Check_spec~0.T_node~0.launch_bt$2 $Check_spec~0.T_node~0.reset_flag$2 $Check_spec~0.T_node~0.p1$2 $Check_spec~0.H_discovery~0.out$2 $Check_spec~1.T_node~0.ok$2 $Check_spec~1.T_node~0.start_bt$2 $Check_spec~1.T_node~0.launch_bt$2 $Check_spec~1.T_node~0.reset_flag$2 $Check_spec~1.T_node~0.p1$2 $Check_spec~1.H_discovery~0.out$2 $~flatten0$2 $~flatten1$2 $~flatten2$2 $~flatten3$2))
(assert true)
