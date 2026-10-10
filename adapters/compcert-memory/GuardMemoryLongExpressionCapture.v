From Stdlib Require Import Bool List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers Zbits.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightRegionProgress.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryLongControl
  GuardMemoryLongRangeCapture.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Capture an actual readonly I64 expression, rather than substituting its
    mathematical affine interpretation. SAFE below is an invocation license;
    acceptance supplies separate interval and exact I32-cache receipts. *)
Definition memory_long_expression_lt code number :=
  Ebinop Olt code (Econst_long (Int64.repr number) memory_long_type) memory_signed_int_type.
Definition memory_long_expression_gt code number :=
  Ebinop Olt (Econst_long (Int64.repr number) memory_long_type) code memory_signed_int_type.
Definition memory_long_expression_accept word lower upper :=
  if Int64.signed word <? lower then false else negb (upper <? Int64.signed word).
Definition memory_long_expression_tree code lower upper :=
  Test (memory_long_expression_lt code lower) (Decision false)
    (Test (memory_long_expression_gt code upper) (Decision false) (Decision true)).
Lemma memory_long_expression_accept_spec word lower upper :
  memory_long_expression_accept word lower upper=true <-> lower<=Int64.signed word<=upper.
Proof.
  unfold memory_long_expression_accept; destruct (Int64.signed word <? lower) eqn:LOWER.
  - apply Z.ltb_lt in LOWER; split; [discriminate|lia].
  - apply Z.ltb_ge in LOWER; rewrite negb_true_iff,Z.ltb_ge; lia.
Qed.
Lemma memory_i32_range_is_i64 value : Int.min_signed<=value<=Int.max_signed ->
  Int64.min_signed<=value<=Int64.max_signed.
Proof. change (-2147483648<=value<=2147483647 -> -9223372036854775808<=value<=9223372036854775807); lia. Qed.
Lemma memory_long_expression_lt_execution ge locals temps memory code word number :
  typeof code=memory_long_type -> eval_expr ge locals temps memory code (Vlong word) ->
  Int.min_signed<=number<=Int.max_signed ->
  expression_test (memory_long_expression_lt code number) (Entry ge locals temps memory)
    (Int64.signed word <? number).
Proof.
  intros TYPE SAFE RANGE; exists (Val.of_bool (Int64.signed word <? number)); split.
  - eapply memory_long_test_execution; [exact TYPE|reflexivity|apply Int64.signed_range|
      apply memory_i32_range_is_i64; exact RANGE|rewrite Int64.repr_signed; exact SAFE|constructor].
  - destruct (Int64.signed word <? number); reflexivity.
Qed.
Lemma memory_long_expression_gt_execution ge locals temps memory code word number :
  typeof code=memory_long_type -> eval_expr ge locals temps memory code (Vlong word) ->
  Int.min_signed<=number<=Int.max_signed ->
  expression_test (memory_long_expression_gt code number) (Entry ge locals temps memory)
    (number <? Int64.signed word).
Proof.
  intros TYPE SAFE RANGE; exists (Val.of_bool (number <? Int64.signed word)); split.
  - eapply memory_long_test_execution; [reflexivity|exact TYPE|
      apply memory_i32_range_is_i64; exact RANGE|apply Int64.signed_range|constructor|
      rewrite Int64.repr_signed; exact SAFE].
  - destruct (number <? Int64.signed word); reflexivity.
Qed.
Theorem memory_long_expression_tree_execution ge locals temps memory code word lower upper :
  typeof code=memory_long_type -> eval_expr ge locals temps memory code (Vlong word) ->
  Int.min_signed<=lower<=Int.max_signed -> Int.min_signed<=upper<=Int.max_signed ->
  decision_run (Entry ge locals temps memory) (memory_long_expression_tree code lower upper)
    (memory_long_expression_accept word lower upper).
Proof.
  intros TYPE SAFE LOWER UPPER; unfold memory_long_expression_tree,memory_long_expression_accept.
  eapply run_test with (b:=(Int64.signed word <? lower)).
  - eapply memory_long_expression_lt_execution; eauto.
  - destruct (Int64.signed word <? lower); [constructor|].
    eapply run_test with (b:=(upper <? Int64.signed word)).
    + eapply memory_long_expression_gt_execution; eauto.
    + destruct (upper <? Int64.signed word); constructor.
Qed.

Lemma memory_long_loword_signed word : Int64.loword word=Int.repr (Int64.signed word).
Proof.
  unfold Int64.loword,Int64.signed.
  destruct (zlt (Int64.unsigned word) Int64.half_modulus); [reflexivity|].
  apply Int.eqm_samerepr; unfold Int.eqm,eqmod; exists 4294967296.
  change (Int64.unsigned word=4294967296*4294967296+(Int64.unsigned word-18446744073709551616)); lia.
Qed.
Theorem memory_long_expression_accepted_i32 word lower upper :
  Int.min_signed<=lower -> upper<=Int.max_signed ->
  memory_long_expression_accept word lower upper=true ->
  Int.signed (Int64.loword word)=Int64.signed word.
Proof.
  intros LOWER UPPER ACCEPT; apply memory_long_expression_accept_spec in ACCEPT.
  rewrite memory_long_loword_signed; apply Int.signed_repr; lia.
Qed.
Definition memory_long_expression_to_int code := Ecast code memory_signed_int_type.
Lemma memory_long_expression_to_int_execution ge locals temps memory code word :
  typeof code=memory_long_type -> eval_expr ge locals temps memory code (Vlong word) ->
  eval_expr ge locals temps memory (memory_long_expression_to_int code) (Vint (Int64.loword word)).
Proof. intros TYPE SAFE; eapply eval_Ecast; [exact SAFE|rewrite TYPE; reflexivity]. Qed.
Definition memory_long_expression_capture code cache flag lower upper :=
  tree_statement (memory_long_expression_tree code lower upper)
    (Ssequence (Sset cache (memory_long_expression_to_int code)) (memory_capture_flag flag true))
    (memory_capture_flag flag false).
Definition memory_long_expression_captured (temps : temp_env) cache flag word lower upper :=
  PTree.set flag (Vint (if memory_long_expression_accept word lower upper then Int.one else Int.zero))
    (if memory_long_expression_accept word lower upper then PTree.set cache (Vint (Int64.loword word)) temps else temps).
Theorem memory_long_expression_capture_execution fe ge locals temps memory code cache flag word lower upper :
  typeof code=memory_long_type -> eval_expr ge locals temps memory code (Vlong word) ->
  Int.min_signed<=lower<=Int.max_signed -> Int.min_signed<=upper<=Int.max_signed ->
  exec_stmt fe ge locals temps memory (memory_long_expression_capture code cache flag lower upper) E0
    (memory_long_expression_captured temps cache flag word lower upper) memory Out_normal.
Proof.
  intros TYPE SAFE LOWER UPPER; unfold memory_long_expression_capture,memory_long_expression_captured.
  eapply decision_fragment_run; [eapply memory_long_expression_tree_execution; eauto|].
  destruct (memory_long_expression_accept word lower upper).
  - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0).
    + constructor; eapply memory_long_expression_to_int_execution; eauto.
    + apply memory_capture_flag_execution.
  - apply memory_capture_flag_execution.
Qed.
Lemma memory_long_expression_capture_writes code cache flag lower upper :
  writes_only [cache;flag] (memory_long_expression_capture code cache flag lower upper).
Proof.
  unfold memory_long_expression_capture,memory_long_expression_tree,memory_capture_flag; cbn [tree_statement].
  repeat first [apply writes_if|apply writes_sequence|apply writes_set]; cbn; auto.
Qed.
Lemma memory_long_expression_captured_frame temps cache flag word lower upper key :
  key<>cache -> key<>flag ->
  (memory_long_expression_captured temps cache flag word lower upper) ! key=temps ! key.
Proof.
  intros CACHE FLAG; unfold memory_long_expression_captured; rewrite PTree.gso by exact FLAG.
  destruct (memory_long_expression_accept word lower upper); [rewrite PTree.gso by exact CACHE|]; reflexivity.
Qed.

Print Assumptions memory_long_expression_accept_spec.
Print Assumptions memory_long_expression_tree_execution.
Print Assumptions memory_long_loword_signed.
Print Assumptions memory_long_expression_accepted_i32.
Print Assumptions memory_long_expression_capture_execution.
Print Assumptions memory_long_expression_capture_writes.
Print Assumptions memory_long_expression_captured_frame.
