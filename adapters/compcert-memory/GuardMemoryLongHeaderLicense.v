From Stdlib Require Import ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightLoopSyntax.
From GuardMemory Require Import GuardMemoryLongControl GuardMemoryLongLoopControl
  GuardMemoryDoubleLocations GuardMemoryDoubleHeaderFrame GuardMemoryObservationDeterminism.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A source execution licenses its first header.  This is a proof receipt,
    not a runtime prefix that executes the source before checking a candidate. *)
Lemma memory_long_first_header fe ge locals temps memory iterator condition body after final :
  normal_statement body = true ->
  exec_stmt fe ge locals temps memory (memory_long_frontend_loop iterator condition body)
    E0 after final Out_normal ->
  exists flag, expression_test condition (Entry ge locals temps memory) flag /\
    (flag = true -> exists body_temps body_memory,
      exec_stmt fe ge locals temps memory body E0 body_temps body_memory Out_normal).
Proof.
  intros NORMAL RUN; inversion RUN; subst.
  all: repeat match goal with EMPTY : _ ** _ = E0 |- _ =>
    apply Eapp_E0_inv in EMPTY as [LEFT RIGHT]; subst
  end.
  all: match goal with HEADER : exec_stmt _ _ _ _ _
    (Ssequence (Sifthenelse _ _ _) _) E0 _ _ _ |- _ =>
    destruct (memory_long_header_decode HEADER) as [flag [TEST BODY]]
  end.
  all: exists flag; split; [exact TEST|intro TRUE; subst flag].
  all: pose proof (@normal_statement_execution fe ge locals body NORMAL _ _ _ _ _ _ BODY)
    as OUTCOME; subst; do 2 eexists; exact BODY.
Qed.

Lemma memory_long_initialized_first_header fe ge locals temps memory iterator condition body after final :
  normal_statement body = true ->
  exec_stmt fe ge locals temps memory (memory_long_initialized_loop iterator condition body)
    E0 after final Out_normal ->
  exists flag, expression_test condition
    (Entry ge locals (PTree.set iterator (Vlong Int64.zero) temps) memory) flag /\
    (flag = true -> exists body_temps body_memory,
      exec_stmt fe ge locals (PTree.set iterator (Vlong Int64.zero) temps) memory
        body E0 body_temps body_memory Out_normal).
Proof.
  intros NORMAL RUN.
  destruct (sequence_normal_decode RUN) as [middle [mem [INIT LOOP]]].
  pose proof (@memory_long_zero_execution ge locals temps memory) as EXPECTED.
  inversion INIT; subst.
  match goal with EVAL : eval_expr _ _ _ _ memory_long_zero ?actual |- _ =>
    pose proof (memory_expression_unique EVAL EXPECTED) as SAME; subst actual
  end.
  eapply memory_long_first_header; eauto.
Qed.

Definition memory_global_long_condition iterator header :=
  Ebinop Olt (Etempvar iterator memory_long_type) (Evar header memory_long_type)
    memory_signed_int_type.

(** The successful comparison itself rules out Vundef and other value kinds.
    Binding or a stable bound alone would not supply this read permission. *)
Theorem memory_global_long_zero_test_license ge locals temps memory iterator header block flag :
  double_global_binding ge locals header block ->
  temps ! iterator = Some (Vlong Int64.zero) ->
  expression_test (memory_global_long_condition iterator header)
    (Entry ge locals temps memory) flag ->
  exists word, Mem.load Mint64 memory block 0 = Some (Vlong word) /\
    flag = (0 <? Int64.signed word).
Proof.
  intros BINDING TEMP [value [EVAL BOOL]].
  destruct (scalar_binary_inv EVAL) as [left [right [LEFT [RIGHT OP]]]].
  apply scalar_temp_inv in LEFT; change (temps ! iterator = Some left) in LEFT.
  rewrite TEMP in LEFT; inversion LEFT; subst left.
  destruct right; try solve [change (None = Some value) in OP; discriminate].
  change (Some (Val.of_bool (Int64.lt Int64.zero i)) = Some value) in OP.
  inversion OP; subst value.
  exists i; split; [eapply memory_global_long_decode; eauto|].
  change (bool_val (Val.of_bool (Int64.lt Int64.zero i)) memory_signed_int_type memory
    = Some flag) in BOOL.
  assert (FLAG : flag = Int64.lt Int64.zero i).
  { destruct (Int64.lt Int64.zero i);
      [change (Some true = Some flag) in BOOL|change (Some false = Some flag) in BOOL]; congruence. }
  rewrite FLAG; unfold Int64.lt; change ((if zlt 0 (Int64.signed i) then true else false)
    = (0 <? Int64.signed i)).
  destruct (zlt 0 (Int64.signed i)); symmetry;
    [apply Z.ltb_lt|apply Z.ltb_ge]; lia.
Qed.

Theorem memory_global_long_initialized_license fe ge locals temps memory iterator header block body after final :
  double_global_binding ge locals header block ->
  normal_statement body = true ->
  exec_stmt fe ge locals temps memory
    (memory_long_initialized_loop iterator (memory_global_long_condition iterator header) body)
    E0 after final Out_normal ->
  exists word, Mem.load Mint64 memory block 0 = Some (Vlong word) /\
    (0 < Int64.signed word -> exists body_temps body_memory,
      exec_stmt fe ge locals (PTree.set iterator (Vlong Int64.zero) temps) memory
        body E0 body_temps body_memory Out_normal).
Proof.
  intros BINDING NORMAL RUN.
  destruct (memory_long_initialized_first_header NORMAL RUN) as [flag [TEST BODY]].
  destruct (@memory_global_long_zero_test_license ge locals
    (PTree.set iterator (Vlong Int64.zero) temps) memory iterator header block flag
    BINDING (PTree.gss _ _ _) TEST) as [word [LOAD FLAG]].
  exists word; split; [exact LOAD|intro POSITIVE; apply BODY; rewrite FLAG; apply Z.ltb_lt; exact POSITIVE].
Qed.

Print Assumptions memory_long_first_header.
Print Assumptions memory_long_initialized_first_header.
Print Assumptions memory_global_long_zero_test_license.
Print Assumptions memory_global_long_initialized_license.
