From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryDoubleSourceTreeData
  GuardMemoryDoubleHeaderFrame GuardMemoryDoubleTreeCaptureData GuardMemoryDoubleTreeCaptureControl
  GuardMemoryLongControl GuardMemoryLongExpressionCapture GuardMemoryRectangularCapture.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition double_tree_flag_value (temps : temp_env) flag (accepted : bool) :=
  temps ! flag=Some (Vint (if accepted then Int.one else Int.zero)).
Inductive double_tree_capture_receipt ge locals memory cache flag lower upper :
    double_source_tree -> temp_env -> temp_env -> bool -> Prop :=
| double_tree_receipt_disabled tree temps : double_tree_flag_value temps flag false ->
    double_tree_capture_receipt ge locals memory cache flag lower upper tree temps temps false
| double_tree_receipt_skip temps : double_tree_flag_value temps flag true ->
    double_tree_capture_receipt ge locals memory cache flag lower upper DoubleTreeSkip temps temps true
| double_tree_receipt_point body instruction temps : double_tree_flag_value temps flag true ->
    double_tree_capture_receipt ge locals memory cache flag lower upper (DoubleTreePoint body instruction) temps temps true
| double_tree_receipt_sequence first second temps middle after accepted_first accepted :
    double_tree_capture_receipt ge locals memory cache flag lower upper first temps middle accepted_first ->
    double_tree_capture_receipt ge locals memory cache flag lower upper second middle after accepted ->
    double_tree_capture_receipt ge locals memory cache flag lower upper (DoubleTreeSequence first second) temps after accepted
| double_tree_receipt_refused raw iterator start bound child temps block input :
    double_tree_flag_value temps flag true ->
    double_global_binding ge locals (tree_bound_header bound) block -> Mem.load Mint64 memory block 0=Some (Vlong input) ->
    Int.min_signed<=lower (tree_bound_header bound)<=Int.max_signed ->
    Int.min_signed<=upper (tree_bound_header bound)<=Int.max_signed ->
    double_tree_capture_accept bound input lower upper=false ->
    double_tree_capture_receipt ge locals memory cache flag lower upper (DoubleTreeRange raw iterator start bound child)
      temps (double_tree_captured temps bound cache flag input lower upper) false
| double_tree_receipt_empty raw iterator start bound child temps block input :
    double_tree_flag_value temps flag true ->
    double_global_binding ge locals (tree_bound_header bound) block -> Mem.load Mint64 memory block 0=Some (Vlong input) ->
    Int.min_signed<=lower (tree_bound_header bound)<=Int.max_signed ->
    Int.min_signed<=upper (tree_bound_header bound)<=Int.max_signed ->
    double_tree_capture_accept bound input lower upper=true -> double_tree_word_active start bound input=false ->
    double_tree_capture_receipt ge locals memory cache flag lower upper (DoubleTreeRange raw iterator start bound child)
      temps (double_tree_captured temps bound cache flag input lower upper) true
| double_tree_receipt_child raw iterator start bound child temps block input after accepted :
    double_tree_flag_value temps flag true ->
    double_global_binding ge locals (tree_bound_header bound) block -> Mem.load Mint64 memory block 0=Some (Vlong input) ->
    Int.min_signed<=lower (tree_bound_header bound)<=Int.max_signed ->
    Int.min_signed<=upper (tree_bound_header bound)<=Int.max_signed ->
    double_tree_capture_accept bound input lower upper=true -> double_tree_word_active start bound input=true ->
    double_tree_capture_receipt ge locals memory cache flag lower upper child
      (double_tree_captured temps bound cache flag input lower upper) after accepted ->
    double_tree_capture_receipt ge locals memory cache flag lower upper (DoubleTreeRange raw iterator start bound child)
      temps after accepted.

Lemma double_tree_capture_receipt_flag ge locals memory cache flag lower upper tree temps after accepted :
  double_tree_capture_receipt ge locals memory cache flag lower upper tree temps after accepted ->
  double_tree_flag_value after flag accepted.
Proof.
  intro RECEIPT; induction RECEIPT; try assumption.
  - unfold double_tree_flag_value; rewrite double_tree_captured_flag,H4; reflexivity.
  - unfold double_tree_flag_value; rewrite double_tree_captured_flag,H4; reflexivity.
Qed.
Lemma double_tree_capture_disabled_execution tree fe ge locals temps memory cache flag lower upper :
  double_tree_flag_value temps flag false ->
  exec_stmt fe ge locals temps memory (double_tree_capture_code tree cache flag lower upper) E0 temps memory Out_normal.
Proof.
  intro FLAG; induction tree; cbn [double_tree_capture_code]; try solve [constructor].
  - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); eassumption.
  - destruct (@rectangular_capture_flag_test ge locals temps memory flag false FLAG) as [value [EVAL BOOL]].
    eapply exec_Sifthenelse with (b:=false); [exact EVAL|exact BOOL|constructor].
Qed.
Theorem double_tree_capture_receipt_execution ge locals memory cache flag lower upper tree temps after accepted :
  double_tree_capture_receipt ge locals memory cache flag lower upper tree temps after accepted ->
  (forall header, In header (double_source_tree_headers tree) -> flag<>cache header) ->
  forall fe, exec_stmt fe ge locals temps memory (double_tree_capture_code tree cache flag lower upper) E0 after memory Out_normal.
Proof.
  intro RECEIPT; induction RECEIPT; intros FRESH fe; cbn [double_tree_capture_code]; try solve [constructor].
  - apply double_tree_capture_disabled_execution; exact H.
  - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0).
    + apply IHRECEIPT1; intros header MEMBER; apply FRESH; cbn; apply in_or_app; left; exact MEMBER.
    + apply IHRECEIPT2; intros header MEMBER; apply FRESH; cbn; apply in_or_app; right; exact MEMBER.
  - destruct (@rectangular_capture_flag_test ge locals temps memory flag true H) as [value [EVAL BOOL]].
    eapply exec_Sifthenelse with (b:=true); [exact EVAL|exact BOOL|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0).
    + unfold double_tree_capture_word; apply memory_long_expression_capture_execution;
        [reflexivity|eapply memory_global_long_execution; eassumption|exact H2|exact H3].
    + pose proof (@double_tree_captured_flag temps bound cache flag input lower upper) as FLAG; rewrite H4 in FLAG.
      destruct (@rectangular_capture_flag_test ge locals _ memory flag false FLAG) as [value' [EVAL' BOOL']].
      eapply exec_Sifthenelse with (b:=false); [exact EVAL'|exact BOOL'|constructor].
  - destruct (@rectangular_capture_flag_test ge locals temps memory flag true H) as [value [EVAL BOOL]].
    eapply exec_Sifthenelse with (b:=true); [exact EVAL|exact BOOL|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0).
    + unfold double_tree_capture_word; apply memory_long_expression_capture_execution;
        [reflexivity|eapply memory_global_long_execution; eassumption|exact H2|exact H3].
    + pose proof (@double_tree_captured_flag temps bound cache flag input lower upper) as FLAG; rewrite H4 in FLAG.
      destruct (@rectangular_capture_flag_test ge locals _ memory flag true FLAG) as [value' [EVAL' BOOL']].
      eapply exec_Sifthenelse with (b:=true); [exact EVAL'|exact BOOL'|].
      destruct (@double_tree_cached_active_execution ge locals _ memory start bound cache input
        (lower (tree_bound_header bound)) (upper (tree_bound_header bound)) (proj1 H2) (proj2 H3) H4
        (@double_tree_captured_cache temps bound cache flag input lower upper (FRESH _ (or_introl eq_refl)) H4))
        as [test [TEST BOOLEAN]]. rewrite H5 in BOOLEAN.
      eapply exec_Sifthenelse with (b:=false); [exact TEST|exact BOOLEAN|constructor].
  - destruct (@rectangular_capture_flag_test ge locals temps memory flag true H) as [value [EVAL BOOL]].
    eapply exec_Sifthenelse with (b:=true); [exact EVAL|exact BOOL|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0).
    + unfold double_tree_capture_word; apply memory_long_expression_capture_execution;
        [reflexivity|eapply memory_global_long_execution; eassumption|exact H2|exact H3].
    + pose proof (@double_tree_captured_flag temps bound cache flag input lower upper) as FLAG; rewrite H4 in FLAG.
      destruct (@rectangular_capture_flag_test ge locals _ memory flag true FLAG) as [value' [EVAL' BOOL']].
      eapply exec_Sifthenelse with (b:=true); [exact EVAL'|exact BOOL'|].
      destruct (@double_tree_cached_active_execution ge locals _ memory start bound cache input
        (lower (tree_bound_header bound)) (upper (tree_bound_header bound)) (proj1 H2) (proj2 H3) H4
        (@double_tree_captured_cache temps bound cache flag input lower upper (FRESH _ (or_introl eq_refl)) H4))
        as [test [TEST BOOLEAN]]. rewrite H5 in BOOLEAN.
      eapply exec_Sifthenelse with (b:=true); [exact TEST|exact BOOLEAN|].
      apply IHRECEIPT; intros header MEMBER; apply FRESH; cbn; right; exact MEMBER.
Qed.
Theorem double_tree_capture_receipt_frame ge locals memory cache flag lower upper tree temps after accepted :
  double_tree_capture_receipt ge locals memory cache flag lower upper tree temps after accepted ->
  (forall header, In header (double_source_tree_headers tree) -> flag<>cache header) ->
  forall key, ~ In key (double_tree_capture_private tree cache flag) -> after ! key=temps ! key.
Proof.
  intros RECEIPT FRESH key PRIVATE.
  eapply writes_only_frame; [exact (@double_tree_capture_receipt_execution ge locals memory cache flag lower upper tree
    temps after accepted RECEIPT FRESH (fun _ _ _ _ _ _ _ => False))|apply double_tree_capture_writes|exact PRIVATE].
Qed.

Print Assumptions double_tree_capture_receipt_flag.
Print Assumptions double_tree_capture_disabled_execution.
Print Assumptions double_tree_capture_receipt_execution.
Print Assumptions double_tree_capture_receipt_frame.
