From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightTempFrame ClightPureExpr ClightSyntaxEquality.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation.
From GuardInterface Require Import CompCertWordObservation.
Import ListNotations.
Set Implicit Arguments.

(** A uniform value may depend on entry words. Its affine evaluation is
    modular; no integer no-wrap premise is needed to preserve an equal word.
    Stores must be typed full int32 dereferences and updates must protect
    every temporary read by the value expression. *)
Fixpoint check_invariant_word_control expression (code:statement) : bool :=
  match code with
  | Sskip | Sbreak | Scontinue => true
  | Sset identifier _ => negb(existsb(Pos.eqb identifier)(memory_source_affine_reads expression))
  | Sassign(Ederef _ lhs_type) rhs =>
      if type_eq lhs_type type_int32s then
        if expression_eq rhs(memory_source_affine_code expression) then true else false
      else false
  | Ssequence first second | Sloop first second =>
      check_invariant_word_control expression first && check_invariant_word_control expression second
  | Sifthenelse _ yes no =>
      check_invariant_word_control expression yes && check_invariant_word_control expression no
  | _ => false end.

Lemma invariant_word_framed_evaluation expression ge locals before memory word after final :
  eval_expr ge locals before memory(memory_source_affine_code expression)(Vint word) ->
  temp_agree(memory_source_affine_reads expression)before after ->
  eval_expr ge locals after final(memory_source_affine_code expression)(Vint word).
Proof.
  intros VALUE FRAME; rewrite(@memory_source_affine_decode expression ge locals before memory word VALUE).
  apply memory_source_affine_evaluation; intros identifier MEMBER.
  rewrite FRAME by exact MEMBER.
  destruct(@memory_source_affine_defined_words expression ge locals before memory word VALUE identifier MEMBER)
    as [input LOOKUP].
  unfold memory_source_word_valuation; rewrite LOOKUP,Int.repr_signed; reflexivity.
Qed.

Lemma invariant_word_set_private expression identifier :
  negb(existsb(Pos.eqb identifier)(memory_source_affine_reads expression))=true ->
  ~In identifier(memory_source_affine_reads expression).
Proof.
  intros CHECK MEMBER; apply negb_true_iff in CHECK.
  assert(FOUND:existsb(Pos.eqb identifier)(memory_source_affine_reads expression)=true).
  { apply existsb_exists; exists identifier; split; [exact MEMBER|apply Pos.eqb_refl]. }
  congruence.
Qed.

Theorem checked_invariant_word_control_execution expression
  fe ge locals before memory code trace after final outcome :
  exec_stmt fe ge locals before memory code trace after final outcome ->
  check_invariant_word_control expression code=true -> forall word,
  eval_expr ge locals before memory(memory_source_affine_code expression)(Vint word) ->
  constant_word_stores word memory final /\
  temp_agree(memory_source_affine_reads expression)before after.
Proof.
  intro RUN; induction RUN; cbn [check_invariant_word_control]; intros CHECK word VALUE;
    try discriminate; try solve [split; [constructor|apply temp_agree_refl]].
  - destruct a1; try discriminate CHECK.
    destruct(type_eq t type_int32s); [subst t|discriminate CHECK].
    destruct(expression_eq a2(memory_source_affine_code expression)); [subst a2|discriminate CHECK].
    assert(SAME:v2=Vint word).
    { eapply pure_scalar_determinate; [apply memory_source_affine_pure|exact H0|exact VALUE]. }
    subst v2; rewrite memory_source_affine_type in H1.
    cbn [type_int32s sem_cast classify_cast cast_int_int] in H1; inversion H1; subst.
    inversion H; subst.
    match goal with STORE:assign_loc _ _ _ _ _ _ _ _ |- _ => inversion STORE; subst end.
    cbn [typeof access_mode type_int32s] in *; try discriminate.
    match goal with MODE:By_value Mint32=By_value _ |- _ => inversion MODE; subst end.
    split; [econstructor; [eapply Mem.storev_store; eassumption|constructor]|apply temp_agree_refl].
  - split; [constructor|apply temp_agree_set; eapply invariant_word_set_private; exact CHECK].
  - apply andb_true_iff in CHECK as [FIRST SECOND].
    destruct(IHRUN1 FIRST word VALUE) as [STORES FRAME].
    destruct(IHRUN2 SECOND word(@invariant_word_framed_evaluation expression ge e le m word le1 m1 VALUE FRAME)) as [TAIL EXIT].
    split; [eapply constant_word_stores_trans|eapply temp_agree_trans]; eassumption.
  - apply andb_true_iff in CHECK as [FIRST SECOND]; apply IHRUN; assumption.
  - apply andb_true_iff in CHECK as [YES NO]; destruct b; cbn in *; apply IHRUN; assumption.
  - apply andb_true_iff in CHECK as [FIRST SECOND]; apply IHRUN; assumption.
  - apply andb_true_iff in CHECK as [FIRST SECOND].
    destruct(IHRUN1 FIRST word VALUE) as [STORES FRAME].
    destruct(IHRUN2 SECOND word(@invariant_word_framed_evaluation expression ge e le m word le1 m1 VALUE FRAME)) as [TAIL EXIT].
    split; [eapply constant_word_stores_trans|eapply temp_agree_trans]; eassumption.
  - apply andb_true_iff in CHECK as [FIRST SECOND].
    destruct(IHRUN1 FIRST word VALUE) as [HEAD FRAME].
    pose proof(@invariant_word_framed_evaluation expression ge e le m word le1 m1 VALUE FRAME) as MIDDLE_VALUE.
    destruct(IHRUN2 SECOND word MIDDLE_VALUE) as [STEP MIDDLE_FRAME].
    destruct(IHRUN3 ltac:(cbn [check_invariant_word_control]; rewrite FIRST,SECOND; reflexivity)
      word(@invariant_word_framed_evaluation expression ge e le1 m1 word le2 m2 MIDDLE_VALUE MIDDLE_FRAME)) as [TAIL LAST_FRAME].
    split.
    + eapply constant_word_stores_trans; [exact HEAD|eapply constant_word_stores_trans; eassumption].
    + eapply temp_agree_trans; [exact FRAME|eapply temp_agree_trans; eassumption].
Qed.

Theorem checked_invariant_word_control_preserves_observation expression
  fe ge locals before memory code trace after final outcome word block offset :
  check_invariant_word_control expression code=true ->
  eval_expr ge locals before memory(memory_source_affine_code expression)(Vint word) ->
  Mem.load Mint32 memory block offset=Some(Vint word) ->
  exec_stmt fe ge locals before memory code trace after final outcome ->
  Mem.load Mint32 final block offset=Some(Vint word).
Proof.
  intros CHECK VALUE LOAD RUN.
  eapply constant_word_stores_preserve_observation; [|exact LOAD].
  exact(proj1(@checked_invariant_word_control_execution expression fe ge locals before memory code
    trace after final outcome RUN CHECK word VALUE)).
Qed.

Print Assumptions invariant_word_framed_evaluation.
Print Assumptions invariant_word_set_private.
Print Assumptions checked_invariant_word_control_execution.
Print Assumptions checked_invariant_word_control_preserves_observation.
