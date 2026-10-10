From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightLoopSyntax ClightTempFrame ClightTempFootprint.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryDoubleHeaderFrame GuardMemoryLongControl
  GuardMemoryLongSourceAffine GuardMemoryLongRangeSource GuardMemoryLongRangeHeader
  GuardMemoryLongExpressionCapture GuardMemoryObservationDeterminism.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The first source test is evaluated after initialization. A read-footprint
    proof transports its bound receipt to the actual check entry. Runtime
    source preexecution is not part of the generated code. *)
Theorem memory_long_source_bound_capture fe ge locals temps memory iterator initial bound body start after final
  cache flag lower upper :
  typeof bound=memory_long_type -> ~ In iterator (expression_temps bound) ->
  eval_expr ge locals temps memory initial (Vlong (Int64.repr start)) ->
  normal_statement body=true ->
  Int.min_signed<=lower<=Int.max_signed -> Int.min_signed<=upper<=Int.max_signed ->
  exec_stmt fe ge locals temps memory
    (memory_long_from_loop iterator initial
      (Ebinop Olt (Etempvar iterator memory_long_type) bound memory_signed_int_type) body)
    E0 after final Out_normal ->
  exists word, eval_expr ge locals temps memory bound (Vlong word) /\
    exec_stmt fe ge locals temps memory (memory_long_expression_capture bound cache flag lower upper) E0
      (memory_long_expression_captured temps cache flag word lower upper) memory Out_normal /\
    (memory_long_expression_accept word lower upper=true ->
      lower<=Int64.signed word<=upper /\ Int.signed (Int64.loword word)=Int64.signed word).
Proof.
  intros TYPE FRESH INITIAL NORMAL LOWER UPPER RUN.
  destruct (@memory_long_from_bound_license fe ge locals temps memory iterator initial bound body start after final
    TYPE INITIAL NORMAL RUN) as [word [SAFE ACTIVE]].
  assert (ENTRY : eval_expr ge locals temps memory bound (Vlong word)).
  { eapply expression_temp_transport with (live:=expression_temps bound); [intros key MEMBER; exact MEMBER| |exact SAFE].
    intros key MEMBER; rewrite PTree.gso; [reflexivity|intro SAME; subst key; contradiction]. }
  exists word; split; [exact ENTRY|split].
  - apply memory_long_expression_capture_execution; assumption.
  - intro ACCEPT; split; [apply memory_long_expression_accept_spec; exact ACCEPT|].
    eapply memory_long_expression_accepted_i32 with (lower:=lower) (upper:=upper); [lia|lia|exact ACCEPT].
Qed.

Lemma memory_long_i32_initial_execution ge locals temps memory start :
  Int.min_signed<=start<=Int.max_signed ->
  eval_expr ge locals temps memory
    (Ecast (Econst_int (Int.repr start) memory_signed_int_type) memory_long_type) (Vlong (Int64.repr start)).
Proof.
  intro RANGE; eapply eval_Ecast; [constructor|].
  change (Some (Vlong (Int64.repr (Int.signed (Int.repr start)))) = Some (Vlong (Int64.repr start))).
  rewrite Int.signed_repr by exact RANGE; reflexivity.
Qed.
Definition memory_long_offset_bound header offset :=
  Ebinop Osub (Evar header memory_long_type) (Econst_int offset memory_signed_int_type) memory_long_type.
Lemma memory_long_offset_bound_temps header offset : expression_temps (memory_long_offset_bound header offset)=[].
Proof. reflexivity. Qed.
Theorem memory_long_offset_bound_execution ge locals temps memory header header_block input offset :
  double_global_binding ge locals header header_block ->
  Mem.load Mint64 memory header_block 0=Some (Vlong input) ->
  eval_expr ge locals temps memory (memory_long_offset_bound header offset)
    (Vlong (Int64.sub input (Int64.repr (Int.signed offset)))).
Proof.
  intros BIND LOAD; eapply eval_Ebinop; [eapply memory_global_long_execution; eauto|constructor|reflexivity].
Qed.
Theorem memory_long_offset_bound_decode ge locals temps memory header header_block offset result :
  double_global_binding ge locals header header_block ->
  eval_expr ge locals temps memory (memory_long_offset_bound header offset) (Vlong result) ->
  exists input, Mem.load Mint64 memory header_block 0=Some (Vlong input) /\
    result=Int64.sub input (Int64.repr (Int.signed offset)).
Proof.
  intros BIND RUN; destruct (scalar_binary_inv RUN) as [left [right [LEFT [RIGHT OP]]]].
  assert (LITERAL : eval_expr ge locals temps memory (Econst_int offset memory_signed_int_type) (Vint offset)) by constructor.
  pose proof (memory_expression_unique RIGHT LITERAL) as SAME; subst right.
  destruct left; try solve [change (None=Some (Vlong result)) in OP; discriminate].
  change (Some (Vlong (Int64.sub i (Int64.repr (Int.signed offset)))) = Some (Vlong result)) in OP.
  inversion OP; subst result; exists i; split; [eapply memory_global_long_decode; eauto|reflexivity].
Qed.

(** A complete source -> safe invocation -> accepted arithmetic receipt for
    the actual N-c source-bound shape. It has no optimizer or native callback;
    body normalization and region installation are separate obligations. *)
Theorem memory_long_offset_source_capture fe ge locals temps memory iterator header header_block offset body start after final
  cache flag lower upper :
  double_global_binding ge locals header header_block ->
  Int.min_signed<=start<=Int.max_signed -> normal_statement body=true ->
  Int.min_signed<=lower<=Int.max_signed -> Int.min_signed<=upper<=Int.max_signed ->
  exec_stmt fe ge locals temps memory
    (memory_long_from_loop iterator
      (Ecast (Econst_int (Int.repr start) memory_signed_int_type) memory_long_type)
      (Ebinop Olt (Etempvar iterator memory_long_type) (memory_long_offset_bound header offset) memory_signed_int_type) body)
    E0 after final Out_normal ->
  exists input result, Mem.load Mint64 memory header_block 0=Some (Vlong input) /\
    result=Int64.sub input (Int64.repr (Int.signed offset)) /\
    exec_stmt fe ge locals temps memory
      (memory_long_expression_capture (memory_long_offset_bound header offset) cache flag lower upper) E0
      (memory_long_expression_captured temps cache flag result lower upper) memory Out_normal /\
    (memory_long_expression_accept result lower upper=true ->
      lower<=Int64.signed result<=upper /\
      Int.signed (Int64.loword result)=Int64.signed result /\
      Int64.signed input-Int.signed offset=Int64.signed result).
Proof.
  intros BIND START NORMAL LOWER UPPER RUN.
  destruct (@memory_long_source_bound_capture fe ge locals temps memory iterator
    (Ecast (Econst_int (Int.repr start) memory_signed_int_type) memory_long_type)
    (memory_long_offset_bound header offset) body start after final cache flag lower upper
    eq_refl ltac:(rewrite memory_long_offset_bound_temps; cbn; auto)
    (@memory_long_i32_initial_execution ge locals temps memory start START) NORMAL LOWER UPPER RUN)
    as [result [SAFE [CAPTURE ACCEPTED]]].
  destruct (@memory_long_offset_bound_decode ge locals temps memory header header_block offset result BIND SAFE)
    as [input [LOAD RESULT]].
  exists input,result; split; [exact LOAD|split; [exact RESULT|split; [exact CAPTURE|]]].
  intro ACCEPT; destruct (ACCEPTED ACCEPT) as [RANGE CACHE].
  split; [exact RANGE|split; [exact CACHE|]].
  apply long_sub_i32_accepted_no_wrap with (result:=result); [exact RESULT|lia].
Qed.

Print Assumptions memory_long_source_bound_capture.
Print Assumptions memory_long_i32_initial_execution.
Print Assumptions memory_long_offset_bound_execution.
Print Assumptions memory_long_offset_bound_decode.
Print Assumptions memory_long_offset_source_capture.
