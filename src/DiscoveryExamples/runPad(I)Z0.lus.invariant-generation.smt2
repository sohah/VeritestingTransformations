(set-option :produce-models true)
(set-option :produce-unsat-cores true)
(define-fun T ((%init Bool) ($sig$0 Int) ($T_node~0.start_bt$0 Bool) ($T_node~0.launch_bt$0 Bool) ($T_node~0.reset_flag$0 Bool) ($T_node~0.p1$0 Bool) ($R_wrapper~0.R_node~0.start_btn_bool$0 Bool) ($R_wrapper~0.R_node~0.launch_btn_bool$0 Bool) ($R_wrapper~0.R_node~0.reset_btn_bool$0 Bool) ($R_wrapper~0.R_node~0.ignition_bool$0 Bool) ($R_wrapper~0.R_node~0.r347_start_btn_1_15_4_bool$0 Bool) ($R_wrapper~0.R_node~0.r347_launch_btn_1_17_4_bool$0 Bool) ($R_wrapper~0.R_node~0.r347_reset_btn_1_9_4_bool$0 Bool) ($R_wrapper~0.R_node~0.r347_ignition_r_1_7_4_bool$0 Bool) ($R_wrapper~0.R_node~0.w14_3$0 Int) ($R_wrapper~0.R_node~0.w12_2$0 Int) ($R_wrapper~0.R_node~0.w13_2$0 Int) ($R_wrapper~0.R_node~0.w14_2$0 Int) ($R_wrapper~0.R_node~0.r347_start_btn_1_3_4$0 Int) ($R_wrapper~0.R_node~0.r347_launch_btn_1_3_4$0 Int) ($R_wrapper~0.R_node~0.r347_launch_btn_1_5_4$0 Int) ($R_wrapper~0.R_node~0.r347_start_btn_1_5_4$0 Int) ($R_wrapper~0.R_node~0.r347_launch_btn_1_7_4$0 Int) ($R_wrapper~0.R_node~0.r347_launch_btn_1_9_4$0 Int) ($R_wrapper~0.R_node~0.r347_start_btn_1_7_4$0 Int) ($R_wrapper~0.R_node~0.r347_launch_btn_1_11_4$0 Int) ($R_wrapper~0.R_node~0.r347_start_btn_1_9_4$0 Int) ($R_wrapper~0.R_node~0.r347_reset_btn_1_4_4$0 Int) ($R_wrapper~0.R_node~0.r347_ignition_r_1_4_4$0 Int) ($R_wrapper~0.R_node~0.r347_reset_btn_1_5_4$0 Int) ($R_wrapper~0.R_node~0.r347_launch_btn_1_13_4$0 Int) ($R_wrapper~0.R_node~0.r347_start_btn_1_11_4$0 Int) ($R_wrapper~0.R_node~0.r347_ignition_r_1_5_4$0 Int) ($R_wrapper~0.R_node~0.r347_launch_btn_1_15_4$0 Int) ($R_wrapper~0.R_node~0.r347_reset_btn_1_7_4$0 Int) ($R_wrapper~0.R_node~0.r347_start_btn_1_13_4$0 Int) ($R_wrapper~0.R_node~0.r347_launch_btn_1_17_4$0 Int) ($R_wrapper~0.R_node~0.r347_ignition_r_1_7_4$0 Int) ($R_wrapper~0.R_node~0.r347_reset_btn_1_9_4$0 Int) ($R_wrapper~0.R_node~0.r347_start_btn_1_15_4$0 Int) ($R_wrapper~0.R_node~0.start_btn$0 Int) ($R_wrapper~0.R_node~0.launch_btn$0 Int) ($R_wrapper~0.R_node~0.reset_btn$0 Int) ($R_wrapper~0.R_node~0.ignition$0 Int) ($sig$1 Int) ($T_node~0.start_bt$1 Bool) ($T_node~0.launch_bt$1 Bool) ($T_node~0.reset_flag$1 Bool) ($T_node~0.p1$1 Bool) ($R_wrapper~0.R_node~0.start_btn_bool$1 Bool) ($R_wrapper~0.R_node~0.launch_btn_bool$1 Bool) ($R_wrapper~0.R_node~0.reset_btn_bool$1 Bool) ($R_wrapper~0.R_node~0.ignition_bool$1 Bool) ($R_wrapper~0.R_node~0.r347_start_btn_1_15_4_bool$1 Bool) ($R_wrapper~0.R_node~0.r347_launch_btn_1_17_4_bool$1 Bool) ($R_wrapper~0.R_node~0.r347_reset_btn_1_9_4_bool$1 Bool) ($R_wrapper~0.R_node~0.r347_ignition_r_1_7_4_bool$1 Bool) ($R_wrapper~0.R_node~0.w14_3$1 Int) ($R_wrapper~0.R_node~0.w12_2$1 Int) ($R_wrapper~0.R_node~0.w13_2$1 Int) ($R_wrapper~0.R_node~0.w14_2$1 Int) ($R_wrapper~0.R_node~0.r347_start_btn_1_3_4$1 Int) ($R_wrapper~0.R_node~0.r347_launch_btn_1_3_4$1 Int) ($R_wrapper~0.R_node~0.r347_launch_btn_1_5_4$1 Int) ($R_wrapper~0.R_node~0.r347_start_btn_1_5_4$1 Int) ($R_wrapper~0.R_node~0.r347_launch_btn_1_7_4$1 Int) ($R_wrapper~0.R_node~0.r347_launch_btn_1_9_4$1 Int) ($R_wrapper~0.R_node~0.r347_start_btn_1_7_4$1 Int) ($R_wrapper~0.R_node~0.r347_launch_btn_1_11_4$1 Int) ($R_wrapper~0.R_node~0.r347_start_btn_1_9_4$1 Int) ($R_wrapper~0.R_node~0.r347_reset_btn_1_4_4$1 Int) ($R_wrapper~0.R_node~0.r347_ignition_r_1_4_4$1 Int) ($R_wrapper~0.R_node~0.r347_reset_btn_1_5_4$1 Int) ($R_wrapper~0.R_node~0.r347_launch_btn_1_13_4$1 Int) ($R_wrapper~0.R_node~0.r347_start_btn_1_11_4$1 Int) ($R_wrapper~0.R_node~0.r347_ignition_r_1_5_4$1 Int) ($R_wrapper~0.R_node~0.r347_launch_btn_1_15_4$1 Int) ($R_wrapper~0.R_node~0.r347_reset_btn_1_7_4$1 Int) ($R_wrapper~0.R_node~0.r347_start_btn_1_13_4$1 Int) ($R_wrapper~0.R_node~0.r347_launch_btn_1_17_4$1 Int) ($R_wrapper~0.R_node~0.r347_ignition_r_1_7_4$1 Int) ($R_wrapper~0.R_node~0.r347_reset_btn_1_9_4$1 Int) ($R_wrapper~0.R_node~0.r347_start_btn_1_15_4$1 Int) ($R_wrapper~0.R_node~0.start_btn$1 Int) ($R_wrapper~0.R_node~0.launch_btn$1 Int) ($R_wrapper~0.R_node~0.reset_btn$1 Int) ($R_wrapper~0.R_node~0.ignition$1 Int)) Bool (and (= $T_node~0.start_bt$1 (ite %init false (ite $T_node~0.reset_flag$0 false (ite (and (and (not $T_node~0.start_bt$0) (not $T_node~0.launch_bt$0)) (= $sig$1 0)) false $T_node~0.start_bt$0)))) (= $T_node~0.launch_bt$1 (ite %init false (ite $T_node~0.reset_flag$0 false (ite (and (and $T_node~0.start_bt$0 (not $T_node~0.launch_bt$0)) (= $sig$1 1)) true $T_node~0.launch_bt$0)))) (= $T_node~0.reset_flag$1 (ite %init false $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4_bool$0)) (= $T_node~0.p1$1 (= $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4_bool$1 (ite %init false (and (and $T_node~0.launch_bt$0 (not $T_node~0.reset_flag$1)) (not $T_node~0.reset_flag$0))))) (= $R_wrapper~0.R_node~0.start_btn_bool$1 (ite %init false $R_wrapper~0.R_node~0.r347_start_btn_1_15_4_bool$0)) (= $R_wrapper~0.R_node~0.launch_btn_bool$1 (ite %init false $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4_bool$0)) (= $R_wrapper~0.R_node~0.reset_btn_bool$1 (ite %init false $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4_bool$0)) (= $R_wrapper~0.R_node~0.ignition_bool$1 (ite %init false $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4_bool$0)) (= $R_wrapper~0.R_node~0.w14_3$1 (ite (or (or (or (not (= $R_wrapper~0.R_node~0.start_btn$1 0)) (and (not (not (= $R_wrapper~0.R_node~0.start_btn$1 0))) (not (= $R_wrapper~0.R_node~0.launch_btn$1 0)))) (and (and (not (not (= $R_wrapper~0.R_node~0.start_btn$1 0))) (not (not (= $R_wrapper~0.R_node~0.launch_btn$1 0)))) (not (= $R_wrapper~0.R_node~0.ignition$1 0)))) (and (and (and (not (not (= $R_wrapper~0.R_node~0.start_btn$1 0))) (not (not (= $R_wrapper~0.R_node~0.launch_btn$1 0)))) (not (not (= $R_wrapper~0.R_node~0.ignition$1 0)))) (not (= $R_wrapper~0.R_node~0.reset_btn$1 0)))) (ite (or (or (or (= $R_wrapper~0.R_node~0.start_btn$1 0) (and (not (= $R_wrapper~0.R_node~0.start_btn$1 0)) (not (= $R_wrapper~0.R_node~0.launch_btn$1 0)))) (and (and (not (= $R_wrapper~0.R_node~0.start_btn$1 0)) (not (not (= $R_wrapper~0.R_node~0.launch_btn$1 0)))) (not (= $R_wrapper~0.R_node~0.ignition$1 0)))) (and (and (and (not (= $R_wrapper~0.R_node~0.start_btn$1 0)) (not (not (= $R_wrapper~0.R_node~0.launch_btn$1 0)))) (not (not (= $R_wrapper~0.R_node~0.ignition$1 0)))) (not (= $R_wrapper~0.R_node~0.reset_btn$1 0)))) (ite (and (and (and (not (= $R_wrapper~0.R_node~0.start_btn$1 0)) (not (= $R_wrapper~0.R_node~0.launch_btn$1 0))) (not (not (= $R_wrapper~0.R_node~0.ignition$1 0)))) (not (not (= $R_wrapper~0.R_node~0.reset_btn$1 0)))) 3 (ite (or (or (or (= $R_wrapper~0.R_node~0.start_btn$1 0) (and (not (= $R_wrapper~0.R_node~0.start_btn$1 0)) (= $R_wrapper~0.R_node~0.launch_btn$1 0))) (and (and (not (= $R_wrapper~0.R_node~0.start_btn$1 0)) (not (= $R_wrapper~0.R_node~0.launch_btn$1 0))) (= $R_wrapper~0.R_node~0.ignition$1 0))) (and (and (and (not (= $R_wrapper~0.R_node~0.start_btn$1 0)) (not (= $R_wrapper~0.R_node~0.launch_btn$1 0))) (not (= $R_wrapper~0.R_node~0.ignition$1 0))) (not (= $R_wrapper~0.R_node~0.reset_btn$1 0)))) (ite (or (or (or (= $R_wrapper~0.R_node~0.start_btn$1 0) (and (not (= $R_wrapper~0.R_node~0.start_btn$1 0)) (= $R_wrapper~0.R_node~0.launch_btn$1 0))) (and (and (not (= $R_wrapper~0.R_node~0.start_btn$1 0)) (not (= $R_wrapper~0.R_node~0.launch_btn$1 0))) (not (= $R_wrapper~0.R_node~0.ignition$1 0)))) (and (and (and (not (= $R_wrapper~0.R_node~0.start_btn$1 0)) (not (= $R_wrapper~0.R_node~0.launch_btn$1 0))) (not (not (= $R_wrapper~0.R_node~0.ignition$1 0)))) (= $R_wrapper~0.R_node~0.reset_btn$1 0))) 7 5) 4)) 2) 1)) (= $R_wrapper~0.R_node~0.w12_2$1 (ite (not (= $sig$1 0)) 0 1)) (= $R_wrapper~0.R_node~0.w13_2$1 (ite (not (= $sig$1 1)) 0 1)) (= $R_wrapper~0.R_node~0.w14_2$1 (ite (or (not (= $R_wrapper~0.R_node~0.w12_2$1 0)) (and (not (not (= $R_wrapper~0.R_node~0.w12_2$1 0))) (not (= $R_wrapper~0.R_node~0.w13_2$1 0)))) 1 0)) (= $R_wrapper~0.R_node~0.r347_start_btn_1_3_4$1 (ite (not (= $R_wrapper~0.R_node~0.w12_2$1 0)) 1 $R_wrapper~0.R_node~0.start_btn$1)) (= $R_wrapper~0.R_node~0.r347_launch_btn_1_3_4$1 (ite (not (= $R_wrapper~0.R_node~0.w13_2$1 0)) 1 $R_wrapper~0.R_node~0.launch_btn$1)) (= $R_wrapper~0.R_node~0.r347_launch_btn_1_5_4$1 (ite (not (not (= $R_wrapper~0.R_node~0.w14_3$1 2))) $R_wrapper~0.R_node~0.r347_launch_btn_1_3_4$1 $R_wrapper~0.R_node~0.launch_btn$1)) (= $R_wrapper~0.R_node~0.r347_start_btn_1_5_4$1 (ite (not (not (= $R_wrapper~0.R_node~0.w14_3$1 1))) $R_wrapper~0.R_node~0.r347_start_btn_1_3_4$1 $R_wrapper~0.R_node~0.start_btn$1)) (= $R_wrapper~0.R_node~0.r347_launch_btn_1_7_4$1 (ite (not (not (= $R_wrapper~0.R_node~0.w14_3$1 1))) $R_wrapper~0.R_node~0.launch_btn$1 $R_wrapper~0.R_node~0.r347_launch_btn_1_5_4$1)) (= $R_wrapper~0.R_node~0.r347_launch_btn_1_9_4$1 (ite (not (= $R_wrapper~0.R_node~0.w14_2$1 0)) $R_wrapper~0.R_node~0.r347_launch_btn_1_7_4$1 $R_wrapper~0.R_node~0.launch_btn$1)) (= $R_wrapper~0.R_node~0.r347_start_btn_1_7_4$1 (ite (not (= $R_wrapper~0.R_node~0.w14_2$1 0)) $R_wrapper~0.R_node~0.r347_start_btn_1_5_4$1 $R_wrapper~0.R_node~0.start_btn$1)) (= $R_wrapper~0.R_node~0.r347_launch_btn_1_11_4$1 (ite (and (not (= $R_wrapper~0.R_node~0.w14_3$1 5)) (not (= $R_wrapper~0.R_node~0.w14_3$1 7))) $R_wrapper~0.R_node~0.r347_launch_btn_1_9_4$1 0)) (= $R_wrapper~0.R_node~0.r347_start_btn_1_9_4$1 (ite (and (not (= $R_wrapper~0.R_node~0.w14_3$1 5)) (not (= $R_wrapper~0.R_node~0.w14_3$1 7))) $R_wrapper~0.R_node~0.r347_start_btn_1_7_4$1 0)) (= $R_wrapper~0.R_node~0.r347_reset_btn_1_4_4$1 (ite (and (not (= $R_wrapper~0.R_node~0.w14_3$1 5)) (not (= $R_wrapper~0.R_node~0.w14_3$1 7))) $R_wrapper~0.R_node~0.reset_btn$1 0)) (= $R_wrapper~0.R_node~0.r347_ignition_r_1_4_4$1 (ite (not (not (= $R_wrapper~0.R_node~0.w14_3$1 4))) 0 $R_wrapper~0.R_node~0.ignition$1)) (= $R_wrapper~0.R_node~0.r347_reset_btn_1_5_4$1 (ite (not (not (= $R_wrapper~0.R_node~0.w14_3$1 4))) 1 $R_wrapper~0.R_node~0.r347_reset_btn_1_4_4$1)) (= $R_wrapper~0.R_node~0.r347_launch_btn_1_13_4$1 (ite (not (not (= $R_wrapper~0.R_node~0.w14_3$1 4))) $R_wrapper~0.R_node~0.launch_btn$1 $R_wrapper~0.R_node~0.r347_launch_btn_1_11_4$1)) (= $R_wrapper~0.R_node~0.r347_start_btn_1_11_4$1 (ite (not (not (= $R_wrapper~0.R_node~0.w14_3$1 4))) $R_wrapper~0.R_node~0.start_btn$1 $R_wrapper~0.R_node~0.r347_start_btn_1_9_4$1)) (= $R_wrapper~0.R_node~0.r347_ignition_r_1_5_4$1 (ite (not (not (= $R_wrapper~0.R_node~0.w14_3$1 3))) 1 $R_wrapper~0.R_node~0.r347_ignition_r_1_4_4$1)) (= $R_wrapper~0.R_node~0.r347_launch_btn_1_15_4$1 (ite (not (not (= $R_wrapper~0.R_node~0.w14_3$1 3))) $R_wrapper~0.R_node~0.launch_btn$1 $R_wrapper~0.R_node~0.r347_launch_btn_1_13_4$1)) (= $R_wrapper~0.R_node~0.r347_reset_btn_1_7_4$1 (ite (not (not (= $R_wrapper~0.R_node~0.w14_3$1 3))) $R_wrapper~0.R_node~0.reset_btn$1 $R_wrapper~0.R_node~0.r347_reset_btn_1_5_4$1)) (= $R_wrapper~0.R_node~0.r347_start_btn_1_13_4$1 (ite (not (not (= $R_wrapper~0.R_node~0.w14_3$1 3))) $R_wrapper~0.R_node~0.start_btn$1 $R_wrapper~0.R_node~0.r347_start_btn_1_11_4$1)) (= $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4$1 (ite (not (= 1 0)) $R_wrapper~0.R_node~0.r347_launch_btn_1_15_4$1 $R_wrapper~0.R_node~0.launch_btn$1)) (= $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4$1 (ite (not (= 1 0)) $R_wrapper~0.R_node~0.r347_ignition_r_1_5_4$1 $R_wrapper~0.R_node~0.ignition$1)) (= $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4$1 (ite (not (= 1 0)) $R_wrapper~0.R_node~0.r347_reset_btn_1_7_4$1 $R_wrapper~0.R_node~0.reset_btn$1)) (= $R_wrapper~0.R_node~0.r347_start_btn_1_15_4$1 (ite (not (= 1 0)) $R_wrapper~0.R_node~0.r347_start_btn_1_13_4$1 $R_wrapper~0.R_node~0.start_btn$1)) (= $R_wrapper~0.R_node~0.start_btn$1 (ite $R_wrapper~0.R_node~0.start_btn_bool$1 1 0)) (= $R_wrapper~0.R_node~0.launch_btn$1 (ite $R_wrapper~0.R_node~0.launch_btn_bool$1 1 0)) (= $R_wrapper~0.R_node~0.reset_btn$1 (ite $R_wrapper~0.R_node~0.reset_btn_bool$1 1 0)) (= $R_wrapper~0.R_node~0.ignition$1 (ite $R_wrapper~0.R_node~0.ignition_bool$1 1 0)) (= $R_wrapper~0.R_node~0.r347_start_btn_1_15_4_bool$1 (ite %init false (ite (= $R_wrapper~0.R_node~0.r347_start_btn_1_15_4$1 1) true false))) (= $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4_bool$1 (ite %init false (ite (= $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4$1 1) true false))) (= $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4_bool$1 (ite %init false (ite (= $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4$1 1) true false))) (= $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4_bool$1 (ite %init false (ite (= $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4$1 1) true false)))))
(declare-fun %init () Bool)
; Proposed 19 candidates
(declare-fun $sig$~1 () Int)
(declare-fun $T_node~0.start_bt$~1 () Bool)
(declare-fun $T_node~0.launch_bt$~1 () Bool)
(declare-fun $T_node~0.reset_flag$~1 () Bool)
(declare-fun $T_node~0.p1$~1 () Bool)
(declare-fun $R_wrapper~0.R_node~0.start_btn_bool$~1 () Bool)
(declare-fun $R_wrapper~0.R_node~0.launch_btn_bool$~1 () Bool)
(declare-fun $R_wrapper~0.R_node~0.reset_btn_bool$~1 () Bool)
(declare-fun $R_wrapper~0.R_node~0.ignition_bool$~1 () Bool)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_15_4_bool$~1 () Bool)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4_bool$~1 () Bool)
(declare-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4_bool$~1 () Bool)
(declare-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4_bool$~1 () Bool)
(declare-fun $R_wrapper~0.R_node~0.w14_3$~1 () Int)
(declare-fun $R_wrapper~0.R_node~0.w12_2$~1 () Int)
(declare-fun $R_wrapper~0.R_node~0.w13_2$~1 () Int)
(declare-fun $R_wrapper~0.R_node~0.w14_2$~1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_3_4$~1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_3_4$~1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_5_4$~1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_5_4$~1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_7_4$~1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_9_4$~1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_7_4$~1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_11_4$~1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_9_4$~1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_4_4$~1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_4_4$~1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_5_4$~1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_13_4$~1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_11_4$~1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_5_4$~1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_15_4$~1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_7_4$~1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_13_4$~1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4$~1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4$~1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4$~1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_15_4$~1 () Int)
(declare-fun $R_wrapper~0.R_node~0.start_btn$~1 () Int)
(declare-fun $R_wrapper~0.R_node~0.launch_btn$~1 () Int)
(declare-fun $R_wrapper~0.R_node~0.reset_btn$~1 () Int)
(declare-fun $R_wrapper~0.R_node~0.ignition$~1 () Int)
(declare-fun $sig$0 () Int)
(declare-fun $T_node~0.start_bt$0 () Bool)
(declare-fun $T_node~0.launch_bt$0 () Bool)
(declare-fun $T_node~0.reset_flag$0 () Bool)
(declare-fun $T_node~0.p1$0 () Bool)
(declare-fun $R_wrapper~0.R_node~0.start_btn_bool$0 () Bool)
(declare-fun $R_wrapper~0.R_node~0.launch_btn_bool$0 () Bool)
(declare-fun $R_wrapper~0.R_node~0.reset_btn_bool$0 () Bool)
(declare-fun $R_wrapper~0.R_node~0.ignition_bool$0 () Bool)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_15_4_bool$0 () Bool)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4_bool$0 () Bool)
(declare-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4_bool$0 () Bool)
(declare-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4_bool$0 () Bool)
(declare-fun $R_wrapper~0.R_node~0.w14_3$0 () Int)
(declare-fun $R_wrapper~0.R_node~0.w12_2$0 () Int)
(declare-fun $R_wrapper~0.R_node~0.w13_2$0 () Int)
(declare-fun $R_wrapper~0.R_node~0.w14_2$0 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_3_4$0 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_3_4$0 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_5_4$0 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_5_4$0 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_7_4$0 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_9_4$0 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_7_4$0 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_11_4$0 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_9_4$0 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_4_4$0 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_4_4$0 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_5_4$0 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_13_4$0 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_11_4$0 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_5_4$0 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_15_4$0 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_7_4$0 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_13_4$0 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4$0 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4$0 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4$0 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_15_4$0 () Int)
(declare-fun $R_wrapper~0.R_node~0.start_btn$0 () Int)
(declare-fun $R_wrapper~0.R_node~0.launch_btn$0 () Int)
(declare-fun $R_wrapper~0.R_node~0.reset_btn$0 () Int)
(declare-fun $R_wrapper~0.R_node~0.ignition$0 () Int)
; K = 1
(push 1)
(assert (T true $sig$~1 $T_node~0.start_bt$~1 $T_node~0.launch_bt$~1 $T_node~0.reset_flag$~1 $T_node~0.p1$~1 $R_wrapper~0.R_node~0.start_btn_bool$~1 $R_wrapper~0.R_node~0.launch_btn_bool$~1 $R_wrapper~0.R_node~0.reset_btn_bool$~1 $R_wrapper~0.R_node~0.ignition_bool$~1 $R_wrapper~0.R_node~0.r347_start_btn_1_15_4_bool$~1 $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4_bool$~1 $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4_bool$~1 $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4_bool$~1 $R_wrapper~0.R_node~0.w14_3$~1 $R_wrapper~0.R_node~0.w12_2$~1 $R_wrapper~0.R_node~0.w13_2$~1 $R_wrapper~0.R_node~0.w14_2$~1 $R_wrapper~0.R_node~0.r347_start_btn_1_3_4$~1 $R_wrapper~0.R_node~0.r347_launch_btn_1_3_4$~1 $R_wrapper~0.R_node~0.r347_launch_btn_1_5_4$~1 $R_wrapper~0.R_node~0.r347_start_btn_1_5_4$~1 $R_wrapper~0.R_node~0.r347_launch_btn_1_7_4$~1 $R_wrapper~0.R_node~0.r347_launch_btn_1_9_4$~1 $R_wrapper~0.R_node~0.r347_start_btn_1_7_4$~1 $R_wrapper~0.R_node~0.r347_launch_btn_1_11_4$~1 $R_wrapper~0.R_node~0.r347_start_btn_1_9_4$~1 $R_wrapper~0.R_node~0.r347_reset_btn_1_4_4$~1 $R_wrapper~0.R_node~0.r347_ignition_r_1_4_4$~1 $R_wrapper~0.R_node~0.r347_reset_btn_1_5_4$~1 $R_wrapper~0.R_node~0.r347_launch_btn_1_13_4$~1 $R_wrapper~0.R_node~0.r347_start_btn_1_11_4$~1 $R_wrapper~0.R_node~0.r347_ignition_r_1_5_4$~1 $R_wrapper~0.R_node~0.r347_launch_btn_1_15_4$~1 $R_wrapper~0.R_node~0.r347_reset_btn_1_7_4$~1 $R_wrapper~0.R_node~0.r347_start_btn_1_13_4$~1 $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4$~1 $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4$~1 $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4$~1 $R_wrapper~0.R_node~0.r347_start_btn_1_15_4$~1 $R_wrapper~0.R_node~0.start_btn$~1 $R_wrapper~0.R_node~0.launch_btn$~1 $R_wrapper~0.R_node~0.reset_btn$~1 $R_wrapper~0.R_node~0.ignition$~1 $sig$0 $T_node~0.start_bt$0 $T_node~0.launch_bt$0 $T_node~0.reset_flag$0 $T_node~0.p1$0 $R_wrapper~0.R_node~0.start_btn_bool$0 $R_wrapper~0.R_node~0.launch_btn_bool$0 $R_wrapper~0.R_node~0.reset_btn_bool$0 $R_wrapper~0.R_node~0.ignition_bool$0 $R_wrapper~0.R_node~0.r347_start_btn_1_15_4_bool$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4_bool$0 $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4_bool$0 $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4_bool$0 $R_wrapper~0.R_node~0.w14_3$0 $R_wrapper~0.R_node~0.w12_2$0 $R_wrapper~0.R_node~0.w13_2$0 $R_wrapper~0.R_node~0.w14_2$0 $R_wrapper~0.R_node~0.r347_start_btn_1_3_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_3_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_5_4$0 $R_wrapper~0.R_node~0.r347_start_btn_1_5_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_7_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_9_4$0 $R_wrapper~0.R_node~0.r347_start_btn_1_7_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_11_4$0 $R_wrapper~0.R_node~0.r347_start_btn_1_9_4$0 $R_wrapper~0.R_node~0.r347_reset_btn_1_4_4$0 $R_wrapper~0.R_node~0.r347_ignition_r_1_4_4$0 $R_wrapper~0.R_node~0.r347_reset_btn_1_5_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_13_4$0 $R_wrapper~0.R_node~0.r347_start_btn_1_11_4$0 $R_wrapper~0.R_node~0.r347_ignition_r_1_5_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_15_4$0 $R_wrapper~0.R_node~0.r347_reset_btn_1_7_4$0 $R_wrapper~0.R_node~0.r347_start_btn_1_13_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4$0 $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4$0 $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4$0 $R_wrapper~0.R_node~0.r347_start_btn_1_15_4$0 $R_wrapper~0.R_node~0.start_btn$0 $R_wrapper~0.R_node~0.launch_btn$0 $R_wrapper~0.R_node~0.reset_btn$0 $R_wrapper~0.R_node~0.ignition$0))
(declare-fun act1 () Bool)
(assert (=> act1 (not (and false $T_node~0.reset_flag$0 (not $T_node~0.reset_flag$0) $R_wrapper~0.R_node~0.start_btn_bool$0 (not $R_wrapper~0.R_node~0.start_btn_bool$0) (>= $sig$0 0) $R_wrapper~0.R_node~0.reset_btn_bool$0 (not $R_wrapper~0.R_node~0.reset_btn_bool$0) $R_wrapper~0.R_node~0.launch_btn_bool$0 (not $R_wrapper~0.R_node~0.launch_btn_bool$0) $T_node~0.start_bt$0 (not $T_node~0.start_bt$0) $T_node~0.p1$0 (not $T_node~0.p1$0) $R_wrapper~0.R_node~0.ignition_bool$0 (not $R_wrapper~0.R_node~0.ignition_bool$0) $T_node~0.launch_bt$0 (not $T_node~0.launch_bt$0)))))
(check-sat act1)
(echo "@DONE")
; Z3: sat
; Z3: @DONE
(get-model)
(echo "@DONE")
; Z3: (model 
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_11_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_5_4$0 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_5_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.w14_3$0 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_7_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_15_4_bool$0 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4_bool$0 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_4_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_15_4$0 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.ignition_bool$0 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_5_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $T_node~0.launch_bt$0 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.w13_2$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_13_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.start_btn$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_15_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.launch_btn_bool$0 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4_bool$0 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4_bool$0 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.reset_btn_bool$0 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_5_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_9_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $sig$0 () Int
; Z3:     0)
; Z3:   (define-fun act1 () Bool
; Z3:     true)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_7_4$0 () Int
; Z3:     1)
; Z3:   (define-fun $T_node~0.start_bt$0 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.w12_2$0 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_7_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_11_4$0 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.launch_btn$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_4_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.reset_btn$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.w14_2$0 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.start_btn_bool$0 () Bool
; Z3:     false)
; Z3:   (define-fun $T_node~0.reset_flag$0 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_9_4$0 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_3_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_13_4$0 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.ignition$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_3_4$0 () Int
; Z3:     1)
; Z3:   (define-fun $T_node~0.p1$0 () Bool
; Z3:     true)
; Z3: )
; Z3: @DONE
; Finished single base step refinement
(declare-fun act2 () Bool)
(assert (=> act2 (not (and (not $T_node~0.reset_flag$0) (not $R_wrapper~0.R_node~0.start_btn_bool$0) (not $R_wrapper~0.R_node~0.reset_btn_bool$0) (not $R_wrapper~0.R_node~0.launch_btn_bool$0) (not $T_node~0.start_bt$0) $T_node~0.p1$0 (not $R_wrapper~0.R_node~0.ignition_bool$0) (not $T_node~0.launch_bt$0) (not $T_node~0.reset_flag$0) (not $R_wrapper~0.R_node~0.start_btn_bool$0) (>= $sig$0 0) (not $R_wrapper~0.R_node~0.reset_btn_bool$0) (not $R_wrapper~0.R_node~0.launch_btn_bool$0) (not $T_node~0.start_bt$0) $T_node~0.p1$0 (not $R_wrapper~0.R_node~0.ignition_bool$0) (not $T_node~0.launch_bt$0) (=> false true)))))
(check-sat act2)
(echo "@DONE")
; Z3: sat
; Z3: @DONE
(get-model)
(echo "@DONE")
; Z3: (model 
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_11_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_5_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_5_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.w14_3$0 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_7_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_15_4_bool$0 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4_bool$0 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_4_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_15_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.ignition_bool$0 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_5_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $T_node~0.launch_bt$0 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.w13_2$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_13_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.start_btn$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_15_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.launch_btn_bool$0 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4_bool$0 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4_bool$0 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.reset_btn_bool$0 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_5_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_9_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $sig$0 () Int
; Z3:     (- 1))
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_7_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $T_node~0.start_bt$0 () Bool
; Z3:     false)
; Z3:   (define-fun act2 () Bool
; Z3:     true)
; Z3:   (define-fun $R_wrapper~0.R_node~0.w12_2$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_7_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_11_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.launch_btn$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_4_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.reset_btn$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.w14_2$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.start_btn_bool$0 () Bool
; Z3:     false)
; Z3:   (define-fun $T_node~0.reset_flag$0 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_9_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_3_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_13_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.ignition$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_3_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $T_node~0.p1$0 () Bool
; Z3:     true)
; Z3: )
; Z3: @DONE
; Finished single base step refinement
(declare-fun act3 () Bool)
(assert (=> act3 (not (and (not $T_node~0.reset_flag$0) (not $R_wrapper~0.R_node~0.start_btn_bool$0) (not $R_wrapper~0.R_node~0.reset_btn_bool$0) (not $R_wrapper~0.R_node~0.launch_btn_bool$0) (not $T_node~0.start_bt$0) $T_node~0.p1$0 (not $R_wrapper~0.R_node~0.ignition_bool$0) (not $T_node~0.launch_bt$0) (not $T_node~0.reset_flag$0) (not $R_wrapper~0.R_node~0.start_btn_bool$0) (not $R_wrapper~0.R_node~0.reset_btn_bool$0) (not $R_wrapper~0.R_node~0.launch_btn_bool$0) (not $T_node~0.start_bt$0) $T_node~0.p1$0 (not $R_wrapper~0.R_node~0.ignition_bool$0) (not $T_node~0.launch_bt$0) (=> false (>= $sig$0 0)) (=> (>= $sig$0 0) true)))))
(check-sat act3)
(echo "@DONE")
; Z3: unsat
; Z3: @DONE
(pop 1)
(declare-fun $sig$1 () Int)
(declare-fun $T_node~0.start_bt$1 () Bool)
(declare-fun $T_node~0.launch_bt$1 () Bool)
(declare-fun $T_node~0.reset_flag$1 () Bool)
(declare-fun $T_node~0.p1$1 () Bool)
(declare-fun $R_wrapper~0.R_node~0.start_btn_bool$1 () Bool)
(declare-fun $R_wrapper~0.R_node~0.launch_btn_bool$1 () Bool)
(declare-fun $R_wrapper~0.R_node~0.reset_btn_bool$1 () Bool)
(declare-fun $R_wrapper~0.R_node~0.ignition_bool$1 () Bool)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_15_4_bool$1 () Bool)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4_bool$1 () Bool)
(declare-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4_bool$1 () Bool)
(declare-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4_bool$1 () Bool)
(declare-fun $R_wrapper~0.R_node~0.w14_3$1 () Int)
(declare-fun $R_wrapper~0.R_node~0.w12_2$1 () Int)
(declare-fun $R_wrapper~0.R_node~0.w13_2$1 () Int)
(declare-fun $R_wrapper~0.R_node~0.w14_2$1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_3_4$1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_3_4$1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_5_4$1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_5_4$1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_7_4$1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_9_4$1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_7_4$1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_11_4$1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_9_4$1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_4_4$1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_4_4$1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_5_4$1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_13_4$1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_11_4$1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_5_4$1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_15_4$1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_7_4$1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_13_4$1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4$1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4$1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4$1 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_15_4$1 () Int)
(declare-fun $R_wrapper~0.R_node~0.start_btn$1 () Int)
(declare-fun $R_wrapper~0.R_node~0.launch_btn$1 () Int)
(declare-fun $R_wrapper~0.R_node~0.reset_btn$1 () Int)
(declare-fun $R_wrapper~0.R_node~0.ignition$1 () Int)
(push 1)
(assert true)
(assert (T %init $sig$~1 $T_node~0.start_bt$~1 $T_node~0.launch_bt$~1 $T_node~0.reset_flag$~1 $T_node~0.p1$~1 $R_wrapper~0.R_node~0.start_btn_bool$~1 $R_wrapper~0.R_node~0.launch_btn_bool$~1 $R_wrapper~0.R_node~0.reset_btn_bool$~1 $R_wrapper~0.R_node~0.ignition_bool$~1 $R_wrapper~0.R_node~0.r347_start_btn_1_15_4_bool$~1 $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4_bool$~1 $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4_bool$~1 $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4_bool$~1 $R_wrapper~0.R_node~0.w14_3$~1 $R_wrapper~0.R_node~0.w12_2$~1 $R_wrapper~0.R_node~0.w13_2$~1 $R_wrapper~0.R_node~0.w14_2$~1 $R_wrapper~0.R_node~0.r347_start_btn_1_3_4$~1 $R_wrapper~0.R_node~0.r347_launch_btn_1_3_4$~1 $R_wrapper~0.R_node~0.r347_launch_btn_1_5_4$~1 $R_wrapper~0.R_node~0.r347_start_btn_1_5_4$~1 $R_wrapper~0.R_node~0.r347_launch_btn_1_7_4$~1 $R_wrapper~0.R_node~0.r347_launch_btn_1_9_4$~1 $R_wrapper~0.R_node~0.r347_start_btn_1_7_4$~1 $R_wrapper~0.R_node~0.r347_launch_btn_1_11_4$~1 $R_wrapper~0.R_node~0.r347_start_btn_1_9_4$~1 $R_wrapper~0.R_node~0.r347_reset_btn_1_4_4$~1 $R_wrapper~0.R_node~0.r347_ignition_r_1_4_4$~1 $R_wrapper~0.R_node~0.r347_reset_btn_1_5_4$~1 $R_wrapper~0.R_node~0.r347_launch_btn_1_13_4$~1 $R_wrapper~0.R_node~0.r347_start_btn_1_11_4$~1 $R_wrapper~0.R_node~0.r347_ignition_r_1_5_4$~1 $R_wrapper~0.R_node~0.r347_launch_btn_1_15_4$~1 $R_wrapper~0.R_node~0.r347_reset_btn_1_7_4$~1 $R_wrapper~0.R_node~0.r347_start_btn_1_13_4$~1 $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4$~1 $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4$~1 $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4$~1 $R_wrapper~0.R_node~0.r347_start_btn_1_15_4$~1 $R_wrapper~0.R_node~0.start_btn$~1 $R_wrapper~0.R_node~0.launch_btn$~1 $R_wrapper~0.R_node~0.reset_btn$~1 $R_wrapper~0.R_node~0.ignition$~1 $sig$0 $T_node~0.start_bt$0 $T_node~0.launch_bt$0 $T_node~0.reset_flag$0 $T_node~0.p1$0 $R_wrapper~0.R_node~0.start_btn_bool$0 $R_wrapper~0.R_node~0.launch_btn_bool$0 $R_wrapper~0.R_node~0.reset_btn_bool$0 $R_wrapper~0.R_node~0.ignition_bool$0 $R_wrapper~0.R_node~0.r347_start_btn_1_15_4_bool$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4_bool$0 $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4_bool$0 $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4_bool$0 $R_wrapper~0.R_node~0.w14_3$0 $R_wrapper~0.R_node~0.w12_2$0 $R_wrapper~0.R_node~0.w13_2$0 $R_wrapper~0.R_node~0.w14_2$0 $R_wrapper~0.R_node~0.r347_start_btn_1_3_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_3_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_5_4$0 $R_wrapper~0.R_node~0.r347_start_btn_1_5_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_7_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_9_4$0 $R_wrapper~0.R_node~0.r347_start_btn_1_7_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_11_4$0 $R_wrapper~0.R_node~0.r347_start_btn_1_9_4$0 $R_wrapper~0.R_node~0.r347_reset_btn_1_4_4$0 $R_wrapper~0.R_node~0.r347_ignition_r_1_4_4$0 $R_wrapper~0.R_node~0.r347_reset_btn_1_5_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_13_4$0 $R_wrapper~0.R_node~0.r347_start_btn_1_11_4$0 $R_wrapper~0.R_node~0.r347_ignition_r_1_5_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_15_4$0 $R_wrapper~0.R_node~0.r347_reset_btn_1_7_4$0 $R_wrapper~0.R_node~0.r347_start_btn_1_13_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4$0 $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4$0 $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4$0 $R_wrapper~0.R_node~0.r347_start_btn_1_15_4$0 $R_wrapper~0.R_node~0.start_btn$0 $R_wrapper~0.R_node~0.launch_btn$0 $R_wrapper~0.R_node~0.reset_btn$0 $R_wrapper~0.R_node~0.ignition$0))
(assert true)
(assert (T false $sig$0 $T_node~0.start_bt$0 $T_node~0.launch_bt$0 $T_node~0.reset_flag$0 $T_node~0.p1$0 $R_wrapper~0.R_node~0.start_btn_bool$0 $R_wrapper~0.R_node~0.launch_btn_bool$0 $R_wrapper~0.R_node~0.reset_btn_bool$0 $R_wrapper~0.R_node~0.ignition_bool$0 $R_wrapper~0.R_node~0.r347_start_btn_1_15_4_bool$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4_bool$0 $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4_bool$0 $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4_bool$0 $R_wrapper~0.R_node~0.w14_3$0 $R_wrapper~0.R_node~0.w12_2$0 $R_wrapper~0.R_node~0.w13_2$0 $R_wrapper~0.R_node~0.w14_2$0 $R_wrapper~0.R_node~0.r347_start_btn_1_3_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_3_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_5_4$0 $R_wrapper~0.R_node~0.r347_start_btn_1_5_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_7_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_9_4$0 $R_wrapper~0.R_node~0.r347_start_btn_1_7_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_11_4$0 $R_wrapper~0.R_node~0.r347_start_btn_1_9_4$0 $R_wrapper~0.R_node~0.r347_reset_btn_1_4_4$0 $R_wrapper~0.R_node~0.r347_ignition_r_1_4_4$0 $R_wrapper~0.R_node~0.r347_reset_btn_1_5_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_13_4$0 $R_wrapper~0.R_node~0.r347_start_btn_1_11_4$0 $R_wrapper~0.R_node~0.r347_ignition_r_1_5_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_15_4$0 $R_wrapper~0.R_node~0.r347_reset_btn_1_7_4$0 $R_wrapper~0.R_node~0.r347_start_btn_1_13_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4$0 $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4$0 $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4$0 $R_wrapper~0.R_node~0.r347_start_btn_1_15_4$0 $R_wrapper~0.R_node~0.start_btn$0 $R_wrapper~0.R_node~0.launch_btn$0 $R_wrapper~0.R_node~0.reset_btn$0 $R_wrapper~0.R_node~0.ignition$0 $sig$1 $T_node~0.start_bt$1 $T_node~0.launch_bt$1 $T_node~0.reset_flag$1 $T_node~0.p1$1 $R_wrapper~0.R_node~0.start_btn_bool$1 $R_wrapper~0.R_node~0.launch_btn_bool$1 $R_wrapper~0.R_node~0.reset_btn_bool$1 $R_wrapper~0.R_node~0.ignition_bool$1 $R_wrapper~0.R_node~0.r347_start_btn_1_15_4_bool$1 $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4_bool$1 $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4_bool$1 $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4_bool$1 $R_wrapper~0.R_node~0.w14_3$1 $R_wrapper~0.R_node~0.w12_2$1 $R_wrapper~0.R_node~0.w13_2$1 $R_wrapper~0.R_node~0.w14_2$1 $R_wrapper~0.R_node~0.r347_start_btn_1_3_4$1 $R_wrapper~0.R_node~0.r347_launch_btn_1_3_4$1 $R_wrapper~0.R_node~0.r347_launch_btn_1_5_4$1 $R_wrapper~0.R_node~0.r347_start_btn_1_5_4$1 $R_wrapper~0.R_node~0.r347_launch_btn_1_7_4$1 $R_wrapper~0.R_node~0.r347_launch_btn_1_9_4$1 $R_wrapper~0.R_node~0.r347_start_btn_1_7_4$1 $R_wrapper~0.R_node~0.r347_launch_btn_1_11_4$1 $R_wrapper~0.R_node~0.r347_start_btn_1_9_4$1 $R_wrapper~0.R_node~0.r347_reset_btn_1_4_4$1 $R_wrapper~0.R_node~0.r347_ignition_r_1_4_4$1 $R_wrapper~0.R_node~0.r347_reset_btn_1_5_4$1 $R_wrapper~0.R_node~0.r347_launch_btn_1_13_4$1 $R_wrapper~0.R_node~0.r347_start_btn_1_11_4$1 $R_wrapper~0.R_node~0.r347_ignition_r_1_5_4$1 $R_wrapper~0.R_node~0.r347_launch_btn_1_15_4$1 $R_wrapper~0.R_node~0.r347_reset_btn_1_7_4$1 $R_wrapper~0.R_node~0.r347_start_btn_1_13_4$1 $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4$1 $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4$1 $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4$1 $R_wrapper~0.R_node~0.r347_start_btn_1_15_4$1 $R_wrapper~0.R_node~0.start_btn$1 $R_wrapper~0.R_node~0.launch_btn$1 $R_wrapper~0.R_node~0.reset_btn$1 $R_wrapper~0.R_node~0.ignition$1))
