From Stdlib Require Import List Bool.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightPureExpr ClightTempFrame ClightTempFootprint.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions.
Import ListNotations.
Set Implicit Arguments.

(** Exact machine-word arithmetic, including variable-by-variable products.
    This is a language service, not an affine model or no-wrap assertion. *)
Inductive word_arithmetic : expr -> Prop :=
| word_arithmetic_constant : forall value,
    word_arithmetic(Econst_int value type_int32s)
| word_arithmetic_temp : forall id,
    word_arithmetic(Etempvar id type_int32s)
| word_arithmetic_binary : forall op first second,
    op=Oadd \/ op=Osub \/ op=Omul ->
    word_arithmetic first -> word_arithmetic second ->
    word_arithmetic(Ebinop op first second type_int32s).

Fixpoint word_arithmetic_check code := match code with
| Econst_int _ ty | Etempvar _ ty => if type_eq ty type_int32s then true else false
| Ebinop op first second ty => if type_eq ty type_int32s then
    (match op with Oadd|Osub|Omul=>true|_=>false end) &&
    word_arithmetic_check first && word_arithmetic_check second
    else false
| _=>false end.

Lemma word_arithmetic_check_sound code : word_arithmetic_check code=true -> word_arithmetic code.
Proof.
  induction code; cbn; try discriminate.
  - destruct(type_eq t type_int32s); [subst; intros; constructor|discriminate].
  - destruct(type_eq t type_int32s); [subst; intros; constructor|discriminate].
  - destruct(type_eq t type_int32s); [subst|discriminate].
    rewrite !andb_true_iff; intros [[OP FIRST] SECOND].
    apply word_arithmetic_binary; [destruct b; cbn in OP; try discriminate; tauto|apply IHcode1|apply IHcode2]; assumption.
Qed.
Lemma word_arithmetic_type code : word_arithmetic code -> typeof code=type_int32s.
Proof. intro WORD; inversion WORD; reflexivity. Qed.
Lemma word_arithmetic_pure code : word_arithmetic code -> pure_scalar code.
Proof. intro WORD; induction WORD; constructor; assumption. Qed.

Fixpoint word_replace (binding : ident->option int) code := match code with
| Etempvar id ty => match binding id with Some value=>Econst_int value ty|None=>code end
| Ebinop op first second ty=>Ebinop op(word_replace binding first)(word_replace binding second)ty
| _=>code end.
Lemma word_replace_type binding code : typeof(word_replace binding code)=typeof code.
Proof. destruct code; cbn; try reflexivity; destruct(binding i); reflexivity. Qed.
Lemma word_replace_arithmetic binding code : word_arithmetic code -> word_arithmetic(word_replace binding code).
Proof.
  intro WORD; induction WORD; cbn [word_replace]; try constructor; try assumption.
  destruct(binding id); constructor.
Qed.
Definition word_replacement_frame binding code before current := forall id,
  In id(expression_temps code) -> match binding id with
  | Some value=>before!id=Some(Vint value)
  | None=>before!id=current!id end.

Theorem word_replacement_evaluation code : word_arithmetic code ->
  forall binding ge locals before memory current target_memory value,
  word_replacement_frame binding code before current ->
  eval_expr ge locals before memory code(Vint value) ->
  eval_expr ge locals current target_memory(word_replace binding code)(Vint value).
Proof.
  intro WORD; induction WORD; intros binding ge locals before memory current target_memory result FRAME SOURCE.
  - apply scalar_const_inv in SOURCE; injection SOURCE as SAME; subst; constructor.
  - apply scalar_temp_inv in SOURCE.
    pose proof(FRAME id(or_introl eq_refl)) as SAME.
    cbn [word_replace]; destruct(binding id)as [replacement|]eqn:LOOKUP.
    + assert(result=replacement)by congruence; subst result; constructor.
    + constructor; congruence.
  - apply scalar_binary_inv in SOURCE as [left [right [FIRST [SECOND OP]]]].
    rewrite(word_arithmetic_type WORD1),(word_arithmetic_type WORD2) in OP.
    destruct(@memory_source_binary_words ge op left right memory result H OP)as [a [b [LEFT RIGHT]]]; subst left right.
    cbn [word_replace]; eapply eval_Ebinop.
    + eapply IHWORD1; [|exact FIRST]. intros id MEMBER; apply FRAME,in_or_app; left; exact MEMBER.
    + eapply IHWORD2; [|exact SECOND]. intros id MEMBER; apply FRAME,in_or_app; right; exact MEMBER.
    + rewrite !word_replace_type,(word_arithmetic_type WORD1),(word_arithmetic_type WORD2).
      destruct H as [SAME|[SAME|SAME]]; subst op; exact OP.
Qed.
Lemma word_replace_none code : word_arithmetic code -> word_replace(fun _=>None)code=code.
Proof. intro WORD; induction WORD; cbn [word_replace]; congruence. Qed.
Theorem word_arithmetic_evaluation_transport code ge locals before memory current target_memory value :
  word_arithmetic code -> temp_agree(expression_temps code)before current ->
  eval_expr ge locals before memory code(Vint value) -> eval_expr ge locals current target_memory code(Vint value).
Proof.
  intros WORD FRAME SOURCE.
  pose proof(@word_replacement_evaluation code WORD(fun _=>None)ge locals before memory current target_memory value
    (fun id MEMBER=>eq_sym(FRAME id MEMBER))SOURCE)as RUN.
  rewrite(word_replace_none WORD)in RUN; exact RUN.
Qed.

Print Assumptions word_arithmetic_check_sound.
Print Assumptions word_arithmetic_type.
Print Assumptions word_arithmetic_pure.
Print Assumptions word_replace_type.
Print Assumptions word_replace_arithmetic.
Print Assumptions word_replacement_evaluation.
Print Assumptions word_arithmetic_evaluation_transport.
