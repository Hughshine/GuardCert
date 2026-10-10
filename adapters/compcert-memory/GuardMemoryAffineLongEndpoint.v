From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From polcert.lib Require Import Linalg.
From Guard Require Import ClightTempFrame ClightSyntaxEquality.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryLongSourceAffine
  GuardMemoryNaryAffineExpressions GuardMemoryLongExpressionCapture.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A source endpoint service for literals and affine expressions in outer
    I64 controls. Parsing and evaluation do not by themselves establish that
    the mathematical value fits I64. The domain must discharge NONWRAP before
    this service can turn accepted machine checks into mathematical facts. *)
Definition affine_long_endpoint_value (row : constraint) (valuation : ident -> Z) (controls : list ident) :=
  memory_nary_index_value row (map valuation controls).
Definition affine_long_endpoint_nonwrap row valuation controls :=
  Int64.min_signed <= affine_long_endpoint_value row valuation controls <= Int64.max_signed.
Definition affine_long_endpoint_words (valuation : ident -> Z) controls (temps : temp_env) :=
  forall identifier, In identifier controls ->
    temps ! identifier = Some (Vlong (Int64.repr (valuation identifier))).

Theorem decoded_affine_long_endpoint_execution controls source row valuation ge locals temps memory :
  decode_long_source_index controls source = Some row ->
  affine_long_endpoint_words valuation controls temps ->
  typeof source = memory_long_type /\
  eval_expr ge locals temps memory source
    (Vlong (Int64.repr (affine_long_endpoint_value row valuation controls))).
Proof.
  intros DECODE WORDS; apply decoded_long_source_index_execution; assumption.
Qed.

Theorem decoded_affine_long_endpoint_signed controls source row valuation ge locals temps memory :
  decode_long_source_index controls source = Some row ->
  affine_long_endpoint_words valuation controls temps ->
  affine_long_endpoint_nonwrap row valuation controls ->
  exists word, eval_expr ge locals temps memory source (Vlong word) /\
    Int64.signed word = affine_long_endpoint_value row valuation controls.
Proof.
  intros DECODE WORDS NONWRAP.
  exists (Int64.repr (affine_long_endpoint_value row valuation controls)); split.
  - exact (proj2 (@decoded_affine_long_endpoint_execution controls source row valuation ge locals temps memory DECODE WORDS)).
  - apply Int64.signed_repr; exact NONWRAP.
Qed.

Theorem affine_long_endpoint_accepted_math controls row valuation lower upper :
  affine_long_endpoint_nonwrap row valuation controls ->
  memory_long_expression_accept
    (Int64.repr (affine_long_endpoint_value row valuation controls)) lower upper = true ->
  lower <= affine_long_endpoint_value row valuation controls <= upper.
Proof.
  intros NONWRAP ACCEPT; apply memory_long_expression_accept_spec in ACCEPT.
  rewrite Int64.signed_repr in ACCEPT by exact NONWRAP; exact ACCEPT.
Qed.

Theorem decoded_affine_long_endpoint_capture controls source row valuation fe ge locals temps memory
  cache flag lower upper :
  decode_long_source_index controls source = Some row ->
  affine_long_endpoint_words valuation controls temps ->
  affine_long_endpoint_nonwrap row valuation controls ->
  Int.min_signed <= lower <= Int.max_signed ->
  Int.min_signed <= upper <= Int.max_signed ->
  let value := affine_long_endpoint_value row valuation controls in
  exec_stmt fe ge locals temps memory
    (memory_long_expression_capture source cache flag lower upper) E0
    (memory_long_expression_captured temps cache flag (Int64.repr value) lower upper)
    memory Out_normal /\
  (memory_long_expression_accept (Int64.repr value) lower upper = true ->
    lower <= value <= upper /\ Int.signed (Int64.loword (Int64.repr value)) = value).
Proof.
  intros DECODE WORDS NONWRAP LOWER UPPER; cbn zeta.
  destruct (@decoded_affine_long_endpoint_execution controls source row valuation ge locals temps memory
    DECODE WORDS) as [TYPE EVAL].
  split.
  - apply memory_long_expression_capture_execution; assumption.
  - intro ACCEPT; split.
    + eapply affine_long_endpoint_accepted_math; eauto.
    + rewrite (@memory_long_expression_accepted_i32 (Int64.repr (affine_long_endpoint_value row valuation controls))
        lower upper ltac:(lia) ltac:(lia) ACCEPT).
      apply Int64.signed_repr; exact NONWRAP.
Qed.

Theorem affine_long_endpoint_capture_preserves_inputs valuation controls temps cache flag word lower upper :
  ~ In cache controls -> ~ In flag controls ->
  affine_long_endpoint_words valuation controls temps ->
  affine_long_endpoint_words valuation controls
    (memory_long_expression_captured temps cache flag word lower upper).
Proof.
  intros CACHE FLAG WORDS identifier MEMBER.
  rewrite memory_long_expression_captured_frame.
  - apply WORDS; exact MEMBER.
  - intro SAME; subst identifier; contradiction.
  - intro SAME; subst identifier; contradiction.
Qed.

Example affine_long_literal_endpoint :
  decode_long_source_index [] (Econst_long (Int64.repr 100) memory_long_type) =
    Some ([],100).
Proof. vm_compute; reflexivity. Qed.
Example affine_long_outer_control_endpoint :
  decode_long_source_index [1%positive] (Etempvar 1%positive memory_long_type) = Some ([1],0).
Proof. vm_compute; reflexivity. Qed.

Print Assumptions decoded_affine_long_endpoint_execution.
Print Assumptions decoded_affine_long_endpoint_signed.
Print Assumptions affine_long_endpoint_accepted_math.
Print Assumptions decoded_affine_long_endpoint_capture.
Print Assumptions affine_long_endpoint_capture_preserves_inputs.
