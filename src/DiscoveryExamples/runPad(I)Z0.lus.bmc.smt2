(set-option :produce-models true)
(set-option :produce-unsat-cores true)
(define-fun T ((%init Bool) ($sig$0 Int) ($T_node~0.start_bt$0 Bool) ($T_node~0.launch_bt$0 Bool) ($T_node~0.reset_flag$0 Bool) ($T_node~0.p1$0 Bool) ($R_wrapper~0.R_node~0.start_btn_bool$0 Bool) ($R_wrapper~0.R_node~0.launch_btn_bool$0 Bool) ($R_wrapper~0.R_node~0.reset_btn_bool$0 Bool) ($R_wrapper~0.R_node~0.ignition_bool$0 Bool) ($R_wrapper~0.R_node~0.r347_start_btn_1_15_4_bool$0 Bool) ($R_wrapper~0.R_node~0.r347_launch_btn_1_17_4_bool$0 Bool) ($R_wrapper~0.R_node~0.r347_reset_btn_1_9_4_bool$0 Bool) ($R_wrapper~0.R_node~0.r347_ignition_r_1_7_4_bool$0 Bool) ($R_wrapper~0.R_node~0.w14_3$0 Int) ($R_wrapper~0.R_node~0.w12_2$0 Int) ($R_wrapper~0.R_node~0.w13_2$0 Int) ($R_wrapper~0.R_node~0.w14_2$0 Int) ($R_wrapper~0.R_node~0.r347_start_btn_1_3_4$0 Int) ($R_wrapper~0.R_node~0.r347_launch_btn_1_3_4$0 Int) ($R_wrapper~0.R_node~0.r347_launch_btn_1_5_4$0 Int) ($R_wrapper~0.R_node~0.r347_start_btn_1_5_4$0 Int) ($R_wrapper~0.R_node~0.r347_launch_btn_1_7_4$0 Int) ($R_wrapper~0.R_node~0.r347_launch_btn_1_9_4$0 Int) ($R_wrapper~0.R_node~0.r347_start_btn_1_7_4$0 Int) ($R_wrapper~0.R_node~0.r347_launch_btn_1_11_4$0 Int) ($R_wrapper~0.R_node~0.r347_start_btn_1_9_4$0 Int) ($R_wrapper~0.R_node~0.r347_reset_btn_1_4_4$0 Int) ($R_wrapper~0.R_node~0.r347_ignition_r_1_4_4$0 Int) ($R_wrapper~0.R_node~0.r347_reset_btn_1_5_4$0 Int) ($R_wrapper~0.R_node~0.r347_launch_btn_1_13_4$0 Int) ($R_wrapper~0.R_node~0.r347_start_btn_1_11_4$0 Int) ($R_wrapper~0.R_node~0.r347_ignition_r_1_5_4$0 Int) ($R_wrapper~0.R_node~0.r347_launch_btn_1_15_4$0 Int) ($R_wrapper~0.R_node~0.r347_reset_btn_1_7_4$0 Int) ($R_wrapper~0.R_node~0.r347_start_btn_1_13_4$0 Int) ($R_wrapper~0.R_node~0.r347_launch_btn_1_17_4$0 Int) ($R_wrapper~0.R_node~0.r347_ignition_r_1_7_4$0 Int) ($R_wrapper~0.R_node~0.r347_reset_btn_1_9_4$0 Int) ($R_wrapper~0.R_node~0.r347_start_btn_1_15_4$0 Int) ($R_wrapper~0.R_node~0.start_btn$0 Int) ($R_wrapper~0.R_node~0.launch_btn$0 Int) ($R_wrapper~0.R_node~0.reset_btn$0 Int) ($R_wrapper~0.R_node~0.ignition$0 Int) ($sig$1 Int) ($T_node~0.start_bt$1 Bool) ($T_node~0.launch_bt$1 Bool) ($T_node~0.reset_flag$1 Bool) ($T_node~0.p1$1 Bool) ($R_wrapper~0.R_node~0.start_btn_bool$1 Bool) ($R_wrapper~0.R_node~0.launch_btn_bool$1 Bool) ($R_wrapper~0.R_node~0.reset_btn_bool$1 Bool) ($R_wrapper~0.R_node~0.ignition_bool$1 Bool) ($R_wrapper~0.R_node~0.r347_start_btn_1_15_4_bool$1 Bool) ($R_wrapper~0.R_node~0.r347_launch_btn_1_17_4_bool$1 Bool) ($R_wrapper~0.R_node~0.r347_reset_btn_1_9_4_bool$1 Bool) ($R_wrapper~0.R_node~0.r347_ignition_r_1_7_4_bool$1 Bool) ($R_wrapper~0.R_node~0.w14_3$1 Int) ($R_wrapper~0.R_node~0.w12_2$1 Int) ($R_wrapper~0.R_node~0.w13_2$1 Int) ($R_wrapper~0.R_node~0.w14_2$1 Int) ($R_wrapper~0.R_node~0.r347_start_btn_1_3_4$1 Int) ($R_wrapper~0.R_node~0.r347_launch_btn_1_3_4$1 Int) ($R_wrapper~0.R_node~0.r347_launch_btn_1_5_4$1 Int) ($R_wrapper~0.R_node~0.r347_start_btn_1_5_4$1 Int) ($R_wrapper~0.R_node~0.r347_launch_btn_1_7_4$1 Int) ($R_wrapper~0.R_node~0.r347_launch_btn_1_9_4$1 Int) ($R_wrapper~0.R_node~0.r347_start_btn_1_7_4$1 Int) ($R_wrapper~0.R_node~0.r347_launch_btn_1_11_4$1 Int) ($R_wrapper~0.R_node~0.r347_start_btn_1_9_4$1 Int) ($R_wrapper~0.R_node~0.r347_reset_btn_1_4_4$1 Int) ($R_wrapper~0.R_node~0.r347_ignition_r_1_4_4$1 Int) ($R_wrapper~0.R_node~0.r347_reset_btn_1_5_4$1 Int) ($R_wrapper~0.R_node~0.r347_launch_btn_1_13_4$1 Int) ($R_wrapper~0.R_node~0.r347_start_btn_1_11_4$1 Int) ($R_wrapper~0.R_node~0.r347_ignition_r_1_5_4$1 Int) ($R_wrapper~0.R_node~0.r347_launch_btn_1_15_4$1 Int) ($R_wrapper~0.R_node~0.r347_reset_btn_1_7_4$1 Int) ($R_wrapper~0.R_node~0.r347_start_btn_1_13_4$1 Int) ($R_wrapper~0.R_node~0.r347_launch_btn_1_17_4$1 Int) ($R_wrapper~0.R_node~0.r347_ignition_r_1_7_4$1 Int) ($R_wrapper~0.R_node~0.r347_reset_btn_1_9_4$1 Int) ($R_wrapper~0.R_node~0.r347_start_btn_1_15_4$1 Int) ($R_wrapper~0.R_node~0.start_btn$1 Int) ($R_wrapper~0.R_node~0.launch_btn$1 Int) ($R_wrapper~0.R_node~0.reset_btn$1 Int) ($R_wrapper~0.R_node~0.ignition$1 Int)) Bool (and (= $T_node~0.start_bt$1 (ite %init false (ite $T_node~0.reset_flag$0 false (ite (and (and (not $T_node~0.start_bt$0) (not $T_node~0.launch_bt$0)) (= $sig$1 0)) false $T_node~0.start_bt$0)))) (= $T_node~0.launch_bt$1 (ite %init false (ite $T_node~0.reset_flag$0 false (ite (and (and $T_node~0.start_bt$0 (not $T_node~0.launch_bt$0)) (= $sig$1 1)) true $T_node~0.launch_bt$0)))) (= $T_node~0.reset_flag$1 (ite %init false $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4_bool$0)) (= $T_node~0.p1$1 (= $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4_bool$1 (ite %init false (and (and $T_node~0.launch_bt$0 (not $T_node~0.reset_flag$1)) (not $T_node~0.reset_flag$0))))) (= $R_wrapper~0.R_node~0.start_btn_bool$1 (ite %init false $R_wrapper~0.R_node~0.r347_start_btn_1_15_4_bool$0)) (= $R_wrapper~0.R_node~0.launch_btn_bool$1 (ite %init false $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4_bool$0)) (= $R_wrapper~0.R_node~0.reset_btn_bool$1 (ite %init false $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4_bool$0)) (= $R_wrapper~0.R_node~0.ignition_bool$1 (ite %init false $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4_bool$0)) (= $R_wrapper~0.R_node~0.w14_3$1 (ite (or (or (or (not (= $R_wrapper~0.R_node~0.start_btn$1 0)) (and (not (not (= $R_wrapper~0.R_node~0.start_btn$1 0))) (not (= $R_wrapper~0.R_node~0.launch_btn$1 0)))) (and (and (not (not (= $R_wrapper~0.R_node~0.start_btn$1 0))) (not (not (= $R_wrapper~0.R_node~0.launch_btn$1 0)))) (not (= $R_wrapper~0.R_node~0.ignition$1 0)))) (and (and (and (not (not (= $R_wrapper~0.R_node~0.start_btn$1 0))) (not (not (= $R_wrapper~0.R_node~0.launch_btn$1 0)))) (not (not (= $R_wrapper~0.R_node~0.ignition$1 0)))) (not (= $R_wrapper~0.R_node~0.reset_btn$1 0)))) (ite (or (or (or (= $R_wrapper~0.R_node~0.start_btn$1 0) (and (not (= $R_wrapper~0.R_node~0.start_btn$1 0)) (not (= $R_wrapper~0.R_node~0.launch_btn$1 0)))) (and (and (not (= $R_wrapper~0.R_node~0.start_btn$1 0)) (not (not (= $R_wrapper~0.R_node~0.launch_btn$1 0)))) (not (= $R_wrapper~0.R_node~0.ignition$1 0)))) (and (and (and (not (= $R_wrapper~0.R_node~0.start_btn$1 0)) (not (not (= $R_wrapper~0.R_node~0.launch_btn$1 0)))) (not (not (= $R_wrapper~0.R_node~0.ignition$1 0)))) (not (= $R_wrapper~0.R_node~0.reset_btn$1 0)))) (ite (and (and (and (not (= $R_wrapper~0.R_node~0.start_btn$1 0)) (not (= $R_wrapper~0.R_node~0.launch_btn$1 0))) (not (not (= $R_wrapper~0.R_node~0.ignition$1 0)))) (not (not (= $R_wrapper~0.R_node~0.reset_btn$1 0)))) 3 (ite (or (or (or (= $R_wrapper~0.R_node~0.start_btn$1 0) (and (not (= $R_wrapper~0.R_node~0.start_btn$1 0)) (= $R_wrapper~0.R_node~0.launch_btn$1 0))) (and (and (not (= $R_wrapper~0.R_node~0.start_btn$1 0)) (not (= $R_wrapper~0.R_node~0.launch_btn$1 0))) (= $R_wrapper~0.R_node~0.ignition$1 0))) (and (and (and (not (= $R_wrapper~0.R_node~0.start_btn$1 0)) (not (= $R_wrapper~0.R_node~0.launch_btn$1 0))) (not (= $R_wrapper~0.R_node~0.ignition$1 0))) (not (= $R_wrapper~0.R_node~0.reset_btn$1 0)))) (ite (or (or (or (= $R_wrapper~0.R_node~0.start_btn$1 0) (and (not (= $R_wrapper~0.R_node~0.start_btn$1 0)) (= $R_wrapper~0.R_node~0.launch_btn$1 0))) (and (and (not (= $R_wrapper~0.R_node~0.start_btn$1 0)) (not (= $R_wrapper~0.R_node~0.launch_btn$1 0))) (not (= $R_wrapper~0.R_node~0.ignition$1 0)))) (and (and (and (not (= $R_wrapper~0.R_node~0.start_btn$1 0)) (not (= $R_wrapper~0.R_node~0.launch_btn$1 0))) (not (not (= $R_wrapper~0.R_node~0.ignition$1 0)))) (= $R_wrapper~0.R_node~0.reset_btn$1 0))) 7 5) 4)) 2) 1)) (= $R_wrapper~0.R_node~0.w12_2$1 (ite (not (= $sig$1 0)) 0 1)) (= $R_wrapper~0.R_node~0.w13_2$1 (ite (not (= $sig$1 1)) 0 1)) (= $R_wrapper~0.R_node~0.w14_2$1 (ite (or (not (= $R_wrapper~0.R_node~0.w12_2$1 0)) (and (not (not (= $R_wrapper~0.R_node~0.w12_2$1 0))) (not (= $R_wrapper~0.R_node~0.w13_2$1 0)))) 1 0)) (= $R_wrapper~0.R_node~0.r347_start_btn_1_3_4$1 (ite (not (= $R_wrapper~0.R_node~0.w12_2$1 0)) 1 $R_wrapper~0.R_node~0.start_btn$1)) (= $R_wrapper~0.R_node~0.r347_launch_btn_1_3_4$1 (ite (not (= $R_wrapper~0.R_node~0.w13_2$1 0)) 1 $R_wrapper~0.R_node~0.launch_btn$1)) (= $R_wrapper~0.R_node~0.r347_launch_btn_1_5_4$1 (ite (not (not (= $R_wrapper~0.R_node~0.w14_3$1 2))) $R_wrapper~0.R_node~0.r347_launch_btn_1_3_4$1 $R_wrapper~0.R_node~0.launch_btn$1)) (= $R_wrapper~0.R_node~0.r347_start_btn_1_5_4$1 (ite (not (not (= $R_wrapper~0.R_node~0.w14_3$1 1))) $R_wrapper~0.R_node~0.r347_start_btn_1_3_4$1 $R_wrapper~0.R_node~0.start_btn$1)) (= $R_wrapper~0.R_node~0.r347_launch_btn_1_7_4$1 (ite (not (not (= $R_wrapper~0.R_node~0.w14_3$1 1))) $R_wrapper~0.R_node~0.launch_btn$1 $R_wrapper~0.R_node~0.r347_launch_btn_1_5_4$1)) (= $R_wrapper~0.R_node~0.r347_launch_btn_1_9_4$1 (ite (not (= $R_wrapper~0.R_node~0.w14_2$1 0)) $R_wrapper~0.R_node~0.r347_launch_btn_1_7_4$1 $R_wrapper~0.R_node~0.launch_btn$1)) (= $R_wrapper~0.R_node~0.r347_start_btn_1_7_4$1 (ite (not (= $R_wrapper~0.R_node~0.w14_2$1 0)) $R_wrapper~0.R_node~0.r347_start_btn_1_5_4$1 $R_wrapper~0.R_node~0.start_btn$1)) (= $R_wrapper~0.R_node~0.r347_launch_btn_1_11_4$1 (ite (and (not (= $R_wrapper~0.R_node~0.w14_3$1 5)) (not (= $R_wrapper~0.R_node~0.w14_3$1 7))) $R_wrapper~0.R_node~0.r347_launch_btn_1_9_4$1 0)) (= $R_wrapper~0.R_node~0.r347_start_btn_1_9_4$1 (ite (and (not (= $R_wrapper~0.R_node~0.w14_3$1 5)) (not (= $R_wrapper~0.R_node~0.w14_3$1 7))) $R_wrapper~0.R_node~0.r347_start_btn_1_7_4$1 0)) (= $R_wrapper~0.R_node~0.r347_reset_btn_1_4_4$1 (ite (and (not (= $R_wrapper~0.R_node~0.w14_3$1 5)) (not (= $R_wrapper~0.R_node~0.w14_3$1 7))) $R_wrapper~0.R_node~0.reset_btn$1 0)) (= $R_wrapper~0.R_node~0.r347_ignition_r_1_4_4$1 (ite (not (not (= $R_wrapper~0.R_node~0.w14_3$1 4))) 0 $R_wrapper~0.R_node~0.ignition$1)) (= $R_wrapper~0.R_node~0.r347_reset_btn_1_5_4$1 (ite (not (not (= $R_wrapper~0.R_node~0.w14_3$1 4))) 1 $R_wrapper~0.R_node~0.r347_reset_btn_1_4_4$1)) (= $R_wrapper~0.R_node~0.r347_launch_btn_1_13_4$1 (ite (not (not (= $R_wrapper~0.R_node~0.w14_3$1 4))) $R_wrapper~0.R_node~0.launch_btn$1 $R_wrapper~0.R_node~0.r347_launch_btn_1_11_4$1)) (= $R_wrapper~0.R_node~0.r347_start_btn_1_11_4$1 (ite (not (not (= $R_wrapper~0.R_node~0.w14_3$1 4))) $R_wrapper~0.R_node~0.start_btn$1 $R_wrapper~0.R_node~0.r347_start_btn_1_9_4$1)) (= $R_wrapper~0.R_node~0.r347_ignition_r_1_5_4$1 (ite (not (not (= $R_wrapper~0.R_node~0.w14_3$1 3))) 1 $R_wrapper~0.R_node~0.r347_ignition_r_1_4_4$1)) (= $R_wrapper~0.R_node~0.r347_launch_btn_1_15_4$1 (ite (not (not (= $R_wrapper~0.R_node~0.w14_3$1 3))) $R_wrapper~0.R_node~0.launch_btn$1 $R_wrapper~0.R_node~0.r347_launch_btn_1_13_4$1)) (= $R_wrapper~0.R_node~0.r347_reset_btn_1_7_4$1 (ite (not (not (= $R_wrapper~0.R_node~0.w14_3$1 3))) $R_wrapper~0.R_node~0.reset_btn$1 $R_wrapper~0.R_node~0.r347_reset_btn_1_5_4$1)) (= $R_wrapper~0.R_node~0.r347_start_btn_1_13_4$1 (ite (not (not (= $R_wrapper~0.R_node~0.w14_3$1 3))) $R_wrapper~0.R_node~0.start_btn$1 $R_wrapper~0.R_node~0.r347_start_btn_1_11_4$1)) (= $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4$1 (ite (not (= 1 0)) $R_wrapper~0.R_node~0.r347_launch_btn_1_15_4$1 $R_wrapper~0.R_node~0.launch_btn$1)) (= $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4$1 (ite (not (= 1 0)) $R_wrapper~0.R_node~0.r347_ignition_r_1_5_4$1 $R_wrapper~0.R_node~0.ignition$1)) (= $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4$1 (ite (not (= 1 0)) $R_wrapper~0.R_node~0.r347_reset_btn_1_7_4$1 $R_wrapper~0.R_node~0.reset_btn$1)) (= $R_wrapper~0.R_node~0.r347_start_btn_1_15_4$1 (ite (not (= 1 0)) $R_wrapper~0.R_node~0.r347_start_btn_1_13_4$1 $R_wrapper~0.R_node~0.start_btn$1)) (= $R_wrapper~0.R_node~0.start_btn$1 (ite $R_wrapper~0.R_node~0.start_btn_bool$1 1 0)) (= $R_wrapper~0.R_node~0.launch_btn$1 (ite $R_wrapper~0.R_node~0.launch_btn_bool$1 1 0)) (= $R_wrapper~0.R_node~0.reset_btn$1 (ite $R_wrapper~0.R_node~0.reset_btn_bool$1 1 0)) (= $R_wrapper~0.R_node~0.ignition$1 (ite $R_wrapper~0.R_node~0.ignition_bool$1 1 0)) (= $R_wrapper~0.R_node~0.r347_start_btn_1_15_4_bool$1 (ite %init false (ite (= $R_wrapper~0.R_node~0.r347_start_btn_1_15_4$1 1) true false))) (= $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4_bool$1 (ite %init false (ite (= $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4$1 1) true false))) (= $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4_bool$1 (ite %init false (ite (= $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4$1 1) true false))) (= $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4_bool$1 (ite %init false (ite (= $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4$1 1) true false)))))
(declare-fun %init () Bool)
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
; K = 1
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
(assert (T true $sig$~1 $T_node~0.start_bt$~1 $T_node~0.launch_bt$~1 $T_node~0.reset_flag$~1 $T_node~0.p1$~1 $R_wrapper~0.R_node~0.start_btn_bool$~1 $R_wrapper~0.R_node~0.launch_btn_bool$~1 $R_wrapper~0.R_node~0.reset_btn_bool$~1 $R_wrapper~0.R_node~0.ignition_bool$~1 $R_wrapper~0.R_node~0.r347_start_btn_1_15_4_bool$~1 $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4_bool$~1 $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4_bool$~1 $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4_bool$~1 $R_wrapper~0.R_node~0.w14_3$~1 $R_wrapper~0.R_node~0.w12_2$~1 $R_wrapper~0.R_node~0.w13_2$~1 $R_wrapper~0.R_node~0.w14_2$~1 $R_wrapper~0.R_node~0.r347_start_btn_1_3_4$~1 $R_wrapper~0.R_node~0.r347_launch_btn_1_3_4$~1 $R_wrapper~0.R_node~0.r347_launch_btn_1_5_4$~1 $R_wrapper~0.R_node~0.r347_start_btn_1_5_4$~1 $R_wrapper~0.R_node~0.r347_launch_btn_1_7_4$~1 $R_wrapper~0.R_node~0.r347_launch_btn_1_9_4$~1 $R_wrapper~0.R_node~0.r347_start_btn_1_7_4$~1 $R_wrapper~0.R_node~0.r347_launch_btn_1_11_4$~1 $R_wrapper~0.R_node~0.r347_start_btn_1_9_4$~1 $R_wrapper~0.R_node~0.r347_reset_btn_1_4_4$~1 $R_wrapper~0.R_node~0.r347_ignition_r_1_4_4$~1 $R_wrapper~0.R_node~0.r347_reset_btn_1_5_4$~1 $R_wrapper~0.R_node~0.r347_launch_btn_1_13_4$~1 $R_wrapper~0.R_node~0.r347_start_btn_1_11_4$~1 $R_wrapper~0.R_node~0.r347_ignition_r_1_5_4$~1 $R_wrapper~0.R_node~0.r347_launch_btn_1_15_4$~1 $R_wrapper~0.R_node~0.r347_reset_btn_1_7_4$~1 $R_wrapper~0.R_node~0.r347_start_btn_1_13_4$~1 $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4$~1 $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4$~1 $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4$~1 $R_wrapper~0.R_node~0.r347_start_btn_1_15_4$~1 $R_wrapper~0.R_node~0.start_btn$~1 $R_wrapper~0.R_node~0.launch_btn$~1 $R_wrapper~0.R_node~0.reset_btn$~1 $R_wrapper~0.R_node~0.ignition$~1 $sig$0 $T_node~0.start_bt$0 $T_node~0.launch_bt$0 $T_node~0.reset_flag$0 $T_node~0.p1$0 $R_wrapper~0.R_node~0.start_btn_bool$0 $R_wrapper~0.R_node~0.launch_btn_bool$0 $R_wrapper~0.R_node~0.reset_btn_bool$0 $R_wrapper~0.R_node~0.ignition_bool$0 $R_wrapper~0.R_node~0.r347_start_btn_1_15_4_bool$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4_bool$0 $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4_bool$0 $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4_bool$0 $R_wrapper~0.R_node~0.w14_3$0 $R_wrapper~0.R_node~0.w12_2$0 $R_wrapper~0.R_node~0.w13_2$0 $R_wrapper~0.R_node~0.w14_2$0 $R_wrapper~0.R_node~0.r347_start_btn_1_3_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_3_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_5_4$0 $R_wrapper~0.R_node~0.r347_start_btn_1_5_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_7_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_9_4$0 $R_wrapper~0.R_node~0.r347_start_btn_1_7_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_11_4$0 $R_wrapper~0.R_node~0.r347_start_btn_1_9_4$0 $R_wrapper~0.R_node~0.r347_reset_btn_1_4_4$0 $R_wrapper~0.R_node~0.r347_ignition_r_1_4_4$0 $R_wrapper~0.R_node~0.r347_reset_btn_1_5_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_13_4$0 $R_wrapper~0.R_node~0.r347_start_btn_1_11_4$0 $R_wrapper~0.R_node~0.r347_ignition_r_1_5_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_15_4$0 $R_wrapper~0.R_node~0.r347_reset_btn_1_7_4$0 $R_wrapper~0.R_node~0.r347_start_btn_1_13_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4$0 $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4$0 $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4$0 $R_wrapper~0.R_node~0.r347_start_btn_1_15_4$0 $R_wrapper~0.R_node~0.start_btn$0 $R_wrapper~0.R_node~0.launch_btn$0 $R_wrapper~0.R_node~0.reset_btn$0 $R_wrapper~0.R_node~0.ignition$0))
(declare-fun act1 () Bool)
(assert (=> act1 (not $T_node~0.p1$0)))
(check-sat act1)
(echo "@DONE")
; Z3: unsat
; Z3: @DONE
(assert $T_node~0.p1$0)
; K = 2
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
(assert (T false $sig$0 $T_node~0.start_bt$0 $T_node~0.launch_bt$0 $T_node~0.reset_flag$0 $T_node~0.p1$0 $R_wrapper~0.R_node~0.start_btn_bool$0 $R_wrapper~0.R_node~0.launch_btn_bool$0 $R_wrapper~0.R_node~0.reset_btn_bool$0 $R_wrapper~0.R_node~0.ignition_bool$0 $R_wrapper~0.R_node~0.r347_start_btn_1_15_4_bool$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4_bool$0 $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4_bool$0 $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4_bool$0 $R_wrapper~0.R_node~0.w14_3$0 $R_wrapper~0.R_node~0.w12_2$0 $R_wrapper~0.R_node~0.w13_2$0 $R_wrapper~0.R_node~0.w14_2$0 $R_wrapper~0.R_node~0.r347_start_btn_1_3_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_3_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_5_4$0 $R_wrapper~0.R_node~0.r347_start_btn_1_5_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_7_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_9_4$0 $R_wrapper~0.R_node~0.r347_start_btn_1_7_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_11_4$0 $R_wrapper~0.R_node~0.r347_start_btn_1_9_4$0 $R_wrapper~0.R_node~0.r347_reset_btn_1_4_4$0 $R_wrapper~0.R_node~0.r347_ignition_r_1_4_4$0 $R_wrapper~0.R_node~0.r347_reset_btn_1_5_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_13_4$0 $R_wrapper~0.R_node~0.r347_start_btn_1_11_4$0 $R_wrapper~0.R_node~0.r347_ignition_r_1_5_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_15_4$0 $R_wrapper~0.R_node~0.r347_reset_btn_1_7_4$0 $R_wrapper~0.R_node~0.r347_start_btn_1_13_4$0 $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4$0 $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4$0 $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4$0 $R_wrapper~0.R_node~0.r347_start_btn_1_15_4$0 $R_wrapper~0.R_node~0.start_btn$0 $R_wrapper~0.R_node~0.launch_btn$0 $R_wrapper~0.R_node~0.reset_btn$0 $R_wrapper~0.R_node~0.ignition$0 $sig$1 $T_node~0.start_bt$1 $T_node~0.launch_bt$1 $T_node~0.reset_flag$1 $T_node~0.p1$1 $R_wrapper~0.R_node~0.start_btn_bool$1 $R_wrapper~0.R_node~0.launch_btn_bool$1 $R_wrapper~0.R_node~0.reset_btn_bool$1 $R_wrapper~0.R_node~0.ignition_bool$1 $R_wrapper~0.R_node~0.r347_start_btn_1_15_4_bool$1 $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4_bool$1 $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4_bool$1 $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4_bool$1 $R_wrapper~0.R_node~0.w14_3$1 $R_wrapper~0.R_node~0.w12_2$1 $R_wrapper~0.R_node~0.w13_2$1 $R_wrapper~0.R_node~0.w14_2$1 $R_wrapper~0.R_node~0.r347_start_btn_1_3_4$1 $R_wrapper~0.R_node~0.r347_launch_btn_1_3_4$1 $R_wrapper~0.R_node~0.r347_launch_btn_1_5_4$1 $R_wrapper~0.R_node~0.r347_start_btn_1_5_4$1 $R_wrapper~0.R_node~0.r347_launch_btn_1_7_4$1 $R_wrapper~0.R_node~0.r347_launch_btn_1_9_4$1 $R_wrapper~0.R_node~0.r347_start_btn_1_7_4$1 $R_wrapper~0.R_node~0.r347_launch_btn_1_11_4$1 $R_wrapper~0.R_node~0.r347_start_btn_1_9_4$1 $R_wrapper~0.R_node~0.r347_reset_btn_1_4_4$1 $R_wrapper~0.R_node~0.r347_ignition_r_1_4_4$1 $R_wrapper~0.R_node~0.r347_reset_btn_1_5_4$1 $R_wrapper~0.R_node~0.r347_launch_btn_1_13_4$1 $R_wrapper~0.R_node~0.r347_start_btn_1_11_4$1 $R_wrapper~0.R_node~0.r347_ignition_r_1_5_4$1 $R_wrapper~0.R_node~0.r347_launch_btn_1_15_4$1 $R_wrapper~0.R_node~0.r347_reset_btn_1_7_4$1 $R_wrapper~0.R_node~0.r347_start_btn_1_13_4$1 $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4$1 $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4$1 $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4$1 $R_wrapper~0.R_node~0.r347_start_btn_1_15_4$1 $R_wrapper~0.R_node~0.start_btn$1 $R_wrapper~0.R_node~0.launch_btn$1 $R_wrapper~0.R_node~0.reset_btn$1 $R_wrapper~0.R_node~0.ignition$1))
(declare-fun act2 () Bool)
(assert (=> act2 (not $T_node~0.p1$1)))
(check-sat act2)
(echo "@DONE")
; Z3: unsat
; Z3: @DONE
(assert $T_node~0.p1$1)
; K = 3
(declare-fun $sig$2 () Int)
(declare-fun $T_node~0.start_bt$2 () Bool)
(declare-fun $T_node~0.launch_bt$2 () Bool)
(declare-fun $T_node~0.reset_flag$2 () Bool)
(declare-fun $T_node~0.p1$2 () Bool)
(declare-fun $R_wrapper~0.R_node~0.start_btn_bool$2 () Bool)
(declare-fun $R_wrapper~0.R_node~0.launch_btn_bool$2 () Bool)
(declare-fun $R_wrapper~0.R_node~0.reset_btn_bool$2 () Bool)
(declare-fun $R_wrapper~0.R_node~0.ignition_bool$2 () Bool)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_15_4_bool$2 () Bool)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4_bool$2 () Bool)
(declare-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4_bool$2 () Bool)
(declare-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4_bool$2 () Bool)
(declare-fun $R_wrapper~0.R_node~0.w14_3$2 () Int)
(declare-fun $R_wrapper~0.R_node~0.w12_2$2 () Int)
(declare-fun $R_wrapper~0.R_node~0.w13_2$2 () Int)
(declare-fun $R_wrapper~0.R_node~0.w14_2$2 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_3_4$2 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_3_4$2 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_5_4$2 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_5_4$2 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_7_4$2 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_9_4$2 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_7_4$2 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_11_4$2 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_9_4$2 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_4_4$2 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_4_4$2 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_5_4$2 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_13_4$2 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_11_4$2 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_5_4$2 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_15_4$2 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_7_4$2 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_13_4$2 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4$2 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4$2 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4$2 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_15_4$2 () Int)
(declare-fun $R_wrapper~0.R_node~0.start_btn$2 () Int)
(declare-fun $R_wrapper~0.R_node~0.launch_btn$2 () Int)
(declare-fun $R_wrapper~0.R_node~0.reset_btn$2 () Int)
(declare-fun $R_wrapper~0.R_node~0.ignition$2 () Int)
(assert (T false $sig$1 $T_node~0.start_bt$1 $T_node~0.launch_bt$1 $T_node~0.reset_flag$1 $T_node~0.p1$1 $R_wrapper~0.R_node~0.start_btn_bool$1 $R_wrapper~0.R_node~0.launch_btn_bool$1 $R_wrapper~0.R_node~0.reset_btn_bool$1 $R_wrapper~0.R_node~0.ignition_bool$1 $R_wrapper~0.R_node~0.r347_start_btn_1_15_4_bool$1 $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4_bool$1 $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4_bool$1 $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4_bool$1 $R_wrapper~0.R_node~0.w14_3$1 $R_wrapper~0.R_node~0.w12_2$1 $R_wrapper~0.R_node~0.w13_2$1 $R_wrapper~0.R_node~0.w14_2$1 $R_wrapper~0.R_node~0.r347_start_btn_1_3_4$1 $R_wrapper~0.R_node~0.r347_launch_btn_1_3_4$1 $R_wrapper~0.R_node~0.r347_launch_btn_1_5_4$1 $R_wrapper~0.R_node~0.r347_start_btn_1_5_4$1 $R_wrapper~0.R_node~0.r347_launch_btn_1_7_4$1 $R_wrapper~0.R_node~0.r347_launch_btn_1_9_4$1 $R_wrapper~0.R_node~0.r347_start_btn_1_7_4$1 $R_wrapper~0.R_node~0.r347_launch_btn_1_11_4$1 $R_wrapper~0.R_node~0.r347_start_btn_1_9_4$1 $R_wrapper~0.R_node~0.r347_reset_btn_1_4_4$1 $R_wrapper~0.R_node~0.r347_ignition_r_1_4_4$1 $R_wrapper~0.R_node~0.r347_reset_btn_1_5_4$1 $R_wrapper~0.R_node~0.r347_launch_btn_1_13_4$1 $R_wrapper~0.R_node~0.r347_start_btn_1_11_4$1 $R_wrapper~0.R_node~0.r347_ignition_r_1_5_4$1 $R_wrapper~0.R_node~0.r347_launch_btn_1_15_4$1 $R_wrapper~0.R_node~0.r347_reset_btn_1_7_4$1 $R_wrapper~0.R_node~0.r347_start_btn_1_13_4$1 $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4$1 $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4$1 $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4$1 $R_wrapper~0.R_node~0.r347_start_btn_1_15_4$1 $R_wrapper~0.R_node~0.start_btn$1 $R_wrapper~0.R_node~0.launch_btn$1 $R_wrapper~0.R_node~0.reset_btn$1 $R_wrapper~0.R_node~0.ignition$1 $sig$2 $T_node~0.start_bt$2 $T_node~0.launch_bt$2 $T_node~0.reset_flag$2 $T_node~0.p1$2 $R_wrapper~0.R_node~0.start_btn_bool$2 $R_wrapper~0.R_node~0.launch_btn_bool$2 $R_wrapper~0.R_node~0.reset_btn_bool$2 $R_wrapper~0.R_node~0.ignition_bool$2 $R_wrapper~0.R_node~0.r347_start_btn_1_15_4_bool$2 $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4_bool$2 $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4_bool$2 $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4_bool$2 $R_wrapper~0.R_node~0.w14_3$2 $R_wrapper~0.R_node~0.w12_2$2 $R_wrapper~0.R_node~0.w13_2$2 $R_wrapper~0.R_node~0.w14_2$2 $R_wrapper~0.R_node~0.r347_start_btn_1_3_4$2 $R_wrapper~0.R_node~0.r347_launch_btn_1_3_4$2 $R_wrapper~0.R_node~0.r347_launch_btn_1_5_4$2 $R_wrapper~0.R_node~0.r347_start_btn_1_5_4$2 $R_wrapper~0.R_node~0.r347_launch_btn_1_7_4$2 $R_wrapper~0.R_node~0.r347_launch_btn_1_9_4$2 $R_wrapper~0.R_node~0.r347_start_btn_1_7_4$2 $R_wrapper~0.R_node~0.r347_launch_btn_1_11_4$2 $R_wrapper~0.R_node~0.r347_start_btn_1_9_4$2 $R_wrapper~0.R_node~0.r347_reset_btn_1_4_4$2 $R_wrapper~0.R_node~0.r347_ignition_r_1_4_4$2 $R_wrapper~0.R_node~0.r347_reset_btn_1_5_4$2 $R_wrapper~0.R_node~0.r347_launch_btn_1_13_4$2 $R_wrapper~0.R_node~0.r347_start_btn_1_11_4$2 $R_wrapper~0.R_node~0.r347_ignition_r_1_5_4$2 $R_wrapper~0.R_node~0.r347_launch_btn_1_15_4$2 $R_wrapper~0.R_node~0.r347_reset_btn_1_7_4$2 $R_wrapper~0.R_node~0.r347_start_btn_1_13_4$2 $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4$2 $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4$2 $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4$2 $R_wrapper~0.R_node~0.r347_start_btn_1_15_4$2 $R_wrapper~0.R_node~0.start_btn$2 $R_wrapper~0.R_node~0.launch_btn$2 $R_wrapper~0.R_node~0.reset_btn$2 $R_wrapper~0.R_node~0.ignition$2))
(declare-fun act3 () Bool)
(assert (=> act3 (not $T_node~0.p1$2)))
(check-sat act3)
(echo "@DONE")
; Z3: unsat
; Z3: @DONE
(assert $T_node~0.p1$2)
; K = 4
(declare-fun $sig$3 () Int)
(declare-fun $T_node~0.start_bt$3 () Bool)
(declare-fun $T_node~0.launch_bt$3 () Bool)
(declare-fun $T_node~0.reset_flag$3 () Bool)
(declare-fun $T_node~0.p1$3 () Bool)
(declare-fun $R_wrapper~0.R_node~0.start_btn_bool$3 () Bool)
(declare-fun $R_wrapper~0.R_node~0.launch_btn_bool$3 () Bool)
(declare-fun $R_wrapper~0.R_node~0.reset_btn_bool$3 () Bool)
(declare-fun $R_wrapper~0.R_node~0.ignition_bool$3 () Bool)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_15_4_bool$3 () Bool)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4_bool$3 () Bool)
(declare-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4_bool$3 () Bool)
(declare-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4_bool$3 () Bool)
(declare-fun $R_wrapper~0.R_node~0.w14_3$3 () Int)
(declare-fun $R_wrapper~0.R_node~0.w12_2$3 () Int)
(declare-fun $R_wrapper~0.R_node~0.w13_2$3 () Int)
(declare-fun $R_wrapper~0.R_node~0.w14_2$3 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_3_4$3 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_3_4$3 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_5_4$3 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_5_4$3 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_7_4$3 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_9_4$3 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_7_4$3 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_11_4$3 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_9_4$3 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_4_4$3 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_4_4$3 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_5_4$3 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_13_4$3 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_11_4$3 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_5_4$3 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_15_4$3 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_7_4$3 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_13_4$3 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4$3 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4$3 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4$3 () Int)
(declare-fun $R_wrapper~0.R_node~0.r347_start_btn_1_15_4$3 () Int)
(declare-fun $R_wrapper~0.R_node~0.start_btn$3 () Int)
(declare-fun $R_wrapper~0.R_node~0.launch_btn$3 () Int)
(declare-fun $R_wrapper~0.R_node~0.reset_btn$3 () Int)
(declare-fun $R_wrapper~0.R_node~0.ignition$3 () Int)
(assert (T false $sig$2 $T_node~0.start_bt$2 $T_node~0.launch_bt$2 $T_node~0.reset_flag$2 $T_node~0.p1$2 $R_wrapper~0.R_node~0.start_btn_bool$2 $R_wrapper~0.R_node~0.launch_btn_bool$2 $R_wrapper~0.R_node~0.reset_btn_bool$2 $R_wrapper~0.R_node~0.ignition_bool$2 $R_wrapper~0.R_node~0.r347_start_btn_1_15_4_bool$2 $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4_bool$2 $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4_bool$2 $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4_bool$2 $R_wrapper~0.R_node~0.w14_3$2 $R_wrapper~0.R_node~0.w12_2$2 $R_wrapper~0.R_node~0.w13_2$2 $R_wrapper~0.R_node~0.w14_2$2 $R_wrapper~0.R_node~0.r347_start_btn_1_3_4$2 $R_wrapper~0.R_node~0.r347_launch_btn_1_3_4$2 $R_wrapper~0.R_node~0.r347_launch_btn_1_5_4$2 $R_wrapper~0.R_node~0.r347_start_btn_1_5_4$2 $R_wrapper~0.R_node~0.r347_launch_btn_1_7_4$2 $R_wrapper~0.R_node~0.r347_launch_btn_1_9_4$2 $R_wrapper~0.R_node~0.r347_start_btn_1_7_4$2 $R_wrapper~0.R_node~0.r347_launch_btn_1_11_4$2 $R_wrapper~0.R_node~0.r347_start_btn_1_9_4$2 $R_wrapper~0.R_node~0.r347_reset_btn_1_4_4$2 $R_wrapper~0.R_node~0.r347_ignition_r_1_4_4$2 $R_wrapper~0.R_node~0.r347_reset_btn_1_5_4$2 $R_wrapper~0.R_node~0.r347_launch_btn_1_13_4$2 $R_wrapper~0.R_node~0.r347_start_btn_1_11_4$2 $R_wrapper~0.R_node~0.r347_ignition_r_1_5_4$2 $R_wrapper~0.R_node~0.r347_launch_btn_1_15_4$2 $R_wrapper~0.R_node~0.r347_reset_btn_1_7_4$2 $R_wrapper~0.R_node~0.r347_start_btn_1_13_4$2 $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4$2 $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4$2 $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4$2 $R_wrapper~0.R_node~0.r347_start_btn_1_15_4$2 $R_wrapper~0.R_node~0.start_btn$2 $R_wrapper~0.R_node~0.launch_btn$2 $R_wrapper~0.R_node~0.reset_btn$2 $R_wrapper~0.R_node~0.ignition$2 $sig$3 $T_node~0.start_bt$3 $T_node~0.launch_bt$3 $T_node~0.reset_flag$3 $T_node~0.p1$3 $R_wrapper~0.R_node~0.start_btn_bool$3 $R_wrapper~0.R_node~0.launch_btn_bool$3 $R_wrapper~0.R_node~0.reset_btn_bool$3 $R_wrapper~0.R_node~0.ignition_bool$3 $R_wrapper~0.R_node~0.r347_start_btn_1_15_4_bool$3 $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4_bool$3 $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4_bool$3 $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4_bool$3 $R_wrapper~0.R_node~0.w14_3$3 $R_wrapper~0.R_node~0.w12_2$3 $R_wrapper~0.R_node~0.w13_2$3 $R_wrapper~0.R_node~0.w14_2$3 $R_wrapper~0.R_node~0.r347_start_btn_1_3_4$3 $R_wrapper~0.R_node~0.r347_launch_btn_1_3_4$3 $R_wrapper~0.R_node~0.r347_launch_btn_1_5_4$3 $R_wrapper~0.R_node~0.r347_start_btn_1_5_4$3 $R_wrapper~0.R_node~0.r347_launch_btn_1_7_4$3 $R_wrapper~0.R_node~0.r347_launch_btn_1_9_4$3 $R_wrapper~0.R_node~0.r347_start_btn_1_7_4$3 $R_wrapper~0.R_node~0.r347_launch_btn_1_11_4$3 $R_wrapper~0.R_node~0.r347_start_btn_1_9_4$3 $R_wrapper~0.R_node~0.r347_reset_btn_1_4_4$3 $R_wrapper~0.R_node~0.r347_ignition_r_1_4_4$3 $R_wrapper~0.R_node~0.r347_reset_btn_1_5_4$3 $R_wrapper~0.R_node~0.r347_launch_btn_1_13_4$3 $R_wrapper~0.R_node~0.r347_start_btn_1_11_4$3 $R_wrapper~0.R_node~0.r347_ignition_r_1_5_4$3 $R_wrapper~0.R_node~0.r347_launch_btn_1_15_4$3 $R_wrapper~0.R_node~0.r347_reset_btn_1_7_4$3 $R_wrapper~0.R_node~0.r347_start_btn_1_13_4$3 $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4$3 $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4$3 $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4$3 $R_wrapper~0.R_node~0.r347_start_btn_1_15_4$3 $R_wrapper~0.R_node~0.start_btn$3 $R_wrapper~0.R_node~0.launch_btn$3 $R_wrapper~0.R_node~0.reset_btn$3 $R_wrapper~0.R_node~0.ignition$3))
(declare-fun act4 () Bool)
(assert (=> act4 (not $T_node~0.p1$3)))
(check-sat act4)
(echo "@DONE")
; Z3: sat
; Z3: @DONE
(get-model)
(echo "@DONE")
; Z3: (model 
; Z3:   (define-fun $R_wrapper~0.R_node~0.ignition_bool$1 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.w14_3$3 () Int
; Z3:     3)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_5_4$0 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_13_4$3 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.start_btn_bool$2 () Bool
; Z3:     true)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_5_4$1 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.w12_2$2 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_13_4$2 () Int
; Z3:     1)
; Z3:   (define-fun $T_node~0.launch_bt$3 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.w13_2$1 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.ignition_bool$0 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_5_4$3 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4_bool$3 () Bool
; Z3:     false)
; Z3:   (define-fun $T_node~0.reset_flag$1 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.ignition_bool$3 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.w13_2$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_13_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.start_btn$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_7_4$1 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_11_4$1 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_4_4$1 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_4_4$2 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4$2 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_4_4$3 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_5_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.ignition$1 () Int
; Z3:     0)
; Z3:   (define-fun $sig$0 () Int
; Z3:     0)
; Z3:   (define-fun act1 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_5_4$1 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_7_4$2 () Int
; Z3:     0)
; Z3:   (define-fun $T_node~0.start_bt$0 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_15_4_bool$1 () Bool
; Z3:     true)
; Z3:   (define-fun act2 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4_bool$2 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_4_4$1 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4$3 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_11_4$0 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_5_4$2 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.start_btn_bool$0 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_13_4$2 () Int
; Z3:     1)
; Z3:   (define-fun $T_node~0.launch_bt$1 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_9_4$0 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_9_4$2 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.w12_2$1 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_11_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_3_4$1 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.w14_3$1 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_4_4$2 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_5_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.reset_btn$3 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_3_4$2 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_11_4$3 () Int
; Z3:     1)
; Z3:   (define-fun $T_node~0.reset_flag$2 () Bool
; Z3:     false)
; Z3:   (define-fun $sig$1 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.w14_2$3 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4$3 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_15_4$2 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_5_4$1 () Int
; Z3:     0)
; Z3:   (define-fun $T_node~0.launch_bt$0 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4$1 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.launch_btn$3 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.w14_2$2 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_15_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.launch_btn_bool$0 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_9_4$3 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_9_4$3 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4_bool$0 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4_bool$0 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4$3 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_9_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_5_4$3 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_15_4$3 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.w12_2$0 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_7_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $T_node~0.start_bt$3 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.reset_btn_bool$2 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_13_4$1 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.launch_btn$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_5_4$2 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_4_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_3_4$1 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_15_4$1 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.reset_btn_bool$1 () Bool
; Z3:     false)
; Z3:   (define-fun $T_node~0.start_bt$2 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.launch_btn$2 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_5_4$2 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_5_4$3 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_7_4$2 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4_bool$1 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_13_4$0 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_3_4$0 () Int
; Z3:     1)
; Z3:   (define-fun $T_node~0.p1$0 () Bool
; Z3:     true)
; Z3:   (define-fun $T_node~0.launch_bt$2 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_11_4$1 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.ignition$3 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4$1 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.w14_3$0 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_7_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $T_node~0.p1$3 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.start_btn_bool$3 () Bool
; Z3:     true)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4_bool$0 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_9_4$1 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.reset_btn$1 () Int
; Z3:     0)
; Z3:   (define-fun act4 () Bool
; Z3:     true)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4$2 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.launch_btn_bool$3 () Bool
; Z3:     true)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_7_4$3 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_15_4$2 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.w13_2$3 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_9_4$1 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_5_4$1 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_13_4$3 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4_bool$3 () Bool
; Z3:     true)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_7_4$0 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.start_btn$1 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.w14_2$1 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_3_4$3 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_9_4_bool$2 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_13_4$1 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.ignition_bool$2 () Bool
; Z3:     false)
; Z3:   (define-fun $T_node~0.reset_flag$3 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.reset_btn_bool$3 () Bool
; Z3:     false)
; Z3:   (define-fun $T_node~0.start_bt$1 () Bool
; Z3:     false)
; Z3:   (define-fun $T_node~0.p1$1 () Bool
; Z3:     true)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_11_4$2 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.w14_3$2 () Int
; Z3:     2)
; Z3:   (define-fun $R_wrapper~0.R_node~0.start_btn$3 () Int
; Z3:     1)
; Z3:   (define-fun $T_node~0.reset_flag$0 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_7_4$3 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.ignition$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_7_4$1 () Int
; Z3:     1)
; Z3:   (define-fun act3 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_3_4$2 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_5_4$2 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_7_4$1 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4_bool$2 () Bool
; Z3:     true)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_15_4_bool$0 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_4_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_15_4$0 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_5_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.start_btn$2 () Int
; Z3:     1)
; Z3:   (define-fun $T_node~0.p1$2 () Bool
; Z3:     true)
; Z3:   (define-fun $R_wrapper~0.R_node~0.reset_btn$2 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4$2 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_7_4$2 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.launch_btn_bool$1 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_15_4_bool$2 () Bool
; Z3:     true)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_11_4$3 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.launch_btn_bool$2 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.reset_btn_bool$0 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_11_4$2 () Int
; Z3:     1)
; Z3:   (define-fun $sig$3 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_3_4$3 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.w13_2$2 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_15_4$3 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_15_4$1 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.launch_btn$1 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_9_4$2 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_7_4$3 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.reset_btn$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_5_4$3 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4_bool$1 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.w14_2$0 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_17_4_bool$3 () Bool
; Z3:     true)
; Z3:   (define-fun $sig$2 () Int
; Z3:     1)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_reset_btn_1_4_4$3 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.w12_2$3 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4_bool$1 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_start_btn_1_15_4_bool$3 () Bool
; Z3:     true)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_launch_btn_1_3_4$0 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.r347_ignition_r_1_7_4$1 () Int
; Z3:     0)
; Z3:   (define-fun $R_wrapper~0.R_node~0.start_btn_bool$1 () Bool
; Z3:     false)
; Z3:   (define-fun $R_wrapper~0.R_node~0.ignition$2 () Int
; Z3:     0)
; Z3: )
; Z3: @DONE
; K = 5
