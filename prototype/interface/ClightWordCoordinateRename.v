From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightPureExpr ClightTempFrame ClightTempFootprint.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions.
From GuardInterface Require Import ClightWordArithmeticTransport ClightDirectWordObservation.
Import ListNotations.
Set Implicit Arguments.

(** Source coordinates and private runtime scan coordinates are different
    temporaries. This mapper preserves exact typed machine-word arithmetic. *)
Fixpoint word_rename (rename:ident->ident) code := match code with
| Etempvar id ty=>Etempvar(rename id)ty
| Ebinop op first second ty=>Ebinop op(word_rename rename first)(word_rename rename second)ty
| _=>code end.
Lemma word_rename_type rename code : typeof(word_rename rename code)=typeof code.
Proof. destruct code; reflexivity. Qed.
Lemma word_rename_arithmetic rename code : word_arithmetic code -> word_arithmetic(word_rename rename code).
Proof. intro WORD; induction WORD; cbn [word_rename]; constructor; assumption. Qed.
Lemma word_rename_temps rename code : word_arithmetic code ->
  expression_temps(word_rename rename code)=map rename(expression_temps code).
Proof. intro WORD; induction WORD; cbn [word_rename expression_temps]; try reflexivity; rewrite map_app; congruence. Qed.
Definition word_rename_frame rename code (before current:temp_env) :=
  forall id,In id(expression_temps code) -> before!id=current!(rename id).

Theorem word_rename_evaluation code : word_arithmetic code ->
  forall rename ge locals before memory current target_memory value,
    word_rename_frame rename code before current ->
    eval_expr ge locals before memory code(Vint value) ->
    eval_expr ge locals current target_memory(word_rename rename code)(Vint value).
Proof.
  intro WORD; induction WORD; intros rename ge locals before memory current target_memory result FRAME SOURCE.
  - apply scalar_const_inv in SOURCE; injection SOURCE as SAME; subst; constructor.
  - apply scalar_temp_inv in SOURCE; cbn [word_rename]; apply eval_Etempvar;
      rewrite <-FRAME by(left; reflexivity); exact SOURCE.
  - apply scalar_binary_inv in SOURCE as [left [right [FIRST [SECOND OP]]]].
    rewrite(word_arithmetic_type WORD1),(word_arithmetic_type WORD2)in OP.
    destruct(@memory_source_binary_words ge op left right memory result H OP)as [a [b [LEFT RIGHT]]]; subst left right.
    cbn [word_rename]; eapply eval_Ebinop.
    + eapply IHWORD1; [|exact FIRST]; intros id MEMBER; apply FRAME,in_or_app; left; exact MEMBER.
    + eapply IHWORD2; [|exact SECOND]; intros id MEMBER; apply FRAME,in_or_app; right; exact MEMBER.
    + rewrite !word_rename_type,(word_arithmetic_type WORD1),(word_arithmetic_type WORD2).
      destruct H as [SAME|[SAME|SAME]]; subst op; exact OP.
Qed.

(** This evaluator computes word values only. It asserts neither pointer
    permission nor mathematical no-wrap, and rejects unsupported syntax. *)
Fixpoint word_evaluate (temps:temp_env) code : option int := match code with
| Econst_int value _=>Some value
| Etempvar id _=>match temps!id with Some(Vint value)=>Some value|_=>None end
| Ebinop op first second _=>match word_evaluate temps first,word_evaluate temps second with
    | Some a,Some b=>match op with Oadd=>Some(Int.add a b)|Osub=>Some(Int.sub a b)|Omul=>Some(Int.mul a b)|_=>None end
    | _,_=>None end
| _=>None end.
Theorem word_evaluate_sound code : word_arithmetic code -> forall temps value,
  word_evaluate temps code=Some value -> forall ge locals memory,eval_expr ge locals temps memory code(Vint value).
Proof.
  intro WORD; induction WORD; intros temps result COMPUTE ge locals memory; cbn [word_evaluate]in COMPUTE.
  - injection COMPUTE as SAME; subst; constructor.
  - destruct(temps!id)as [value|]eqn:TEMP; [destruct value|]; try discriminate.
    injection COMPUTE as SAME; subst; constructor; exact TEMP.
  - destruct(word_evaluate temps first)as [a|]eqn:FIRST;
      destruct(word_evaluate temps second)as [b|]eqn:SECOND; try discriminate.
    destruct H as [SAME|[SAME|SAME]]; subst op; injection COMPUTE as SAME; subst result.
    all: eapply eval_Ebinop; [apply IHWORD1; exact FIRST|apply IHWORD2; exact SECOND|
      rewrite(word_arithmetic_type WORD1),(word_arithmetic_type WORD2); reflexivity].
Qed.
Theorem word_evaluate_complete code : word_arithmetic code -> forall ge locals temps memory value,
  eval_expr ge locals temps memory code(Vint value) -> word_evaluate temps code=Some value.
Proof.
  intro WORD; induction WORD; intros ge locals temps memory result SOURCE.
  - apply scalar_const_inv in SOURCE; injection SOURCE as SAME; subst; reflexivity.
  - apply scalar_temp_inv in SOURCE; cbn [word_evaluate]; rewrite SOURCE; reflexivity.
  - apply scalar_binary_inv in SOURCE as [left [right [FIRST [SECOND OP]]]].
    rewrite(word_arithmetic_type WORD1),(word_arithmetic_type WORD2)in OP.
    destruct(@memory_source_binary_words ge op left right memory result H OP)as [a [b [LEFT RIGHT]]]; subst left right.
    cbn [word_evaluate]; rewrite(IHWORD1 _ _ _ _ _ FIRST),(IHWORD2 _ _ _ _ _ SECOND).
    destruct H as [SAME|[SAME|SAME]]; subst op.
    + change (Some(Vint(Int.add a b))=Some(Vint result)) in OP.
      injection OP as SAME; rewrite SAME; reflexivity.
    + change (Some(Vint(Int.sub a b))=Some(Vint result)) in OP.
      injection OP as SAME; rewrite SAME; reflexivity.
    + change (Some(Vint(Int.mul a b))=Some(Vint result)) in OP.
      injection OP as SAME; rewrite SAME; reflexivity.
Qed.

Lemma word_evaluate_frame code : word_arithmetic code -> forall before current,
  temp_agree(expression_temps code) before current ->
  word_evaluate current code=word_evaluate before code.
Proof.
  intro WORD; induction WORD; intros before current FRAME; cbn [word_evaluate].
  - reflexivity.
  - rewrite FRAME by(left; reflexivity); reflexivity.
  - rewrite IHWORD1 with(before:=before),IHWORD2 with(before:=before); try reflexivity.
    + intros id MEMBER; apply FRAME,in_or_app; right; exact MEMBER.
    + intros id MEMBER; apply FRAME,in_or_app; left; exact MEMBER.
Qed.

Definition word_pointer_offset base word :=
  Ptrofs.add base(Ptrofs.mul(Ptrofs.repr 4)(Ptrofs.repr(Int.signed word))).
Definition word_address_evaluate temps pointer index := match temps!pointer,word_evaluate temps index with
| Some(Vptr block base),Some word=>Some(block,word_pointer_offset base word)
| _,_=>None end.
Theorem word_address_evaluate_complete pointer index ge locals temps memory block offset :
  word_arithmetic index ->
  eval_expr ge locals temps memory(direct_word_address pointer index)(Vptr block offset) ->
  word_address_evaluate temps pointer index=Some(block,offset).
Proof.
  intros WORD SOURCE; destruct(direct_word_address_operands WORD SOURCE)as [base [word [PTR [INDEX OP]]]].
  unfold word_address_evaluate; rewrite PTR,(@word_evaluate_complete _ WORD _ _ _ _ _ INDEX).
  change(Some(Vptr block(word_pointer_offset base word))=Some(Vptr block offset))in OP.
  injection OP as SAME; rewrite SAME; reflexivity.
Qed.
Theorem word_address_evaluate_sound pointer index temps block offset :
  word_arithmetic index -> word_address_evaluate temps pointer index=Some(block,offset) ->
  forall ge locals memory,eval_expr ge locals temps memory(direct_word_address pointer index)(Vptr block offset).
Proof.
  intros WORD; unfold word_address_evaluate; destruct(temps!pointer)as [value|]eqn:PTR;
    [destruct value|]; try discriminate.
  destruct(word_evaluate temps index)as [word|]eqn:INDEX; [|discriminate].
  intro SAME; injection SAME as BLOCK OFFSET; subst block offset; intros ge locals memory.
  eapply eval_Ebinop; [apply eval_Etempvar; exact PTR|eapply word_evaluate_sound; eassumption|].
  rewrite(word_arithmetic_type WORD); reflexivity.
Qed.

Lemma word_address_evaluate_frame pointer index before current : word_arithmetic index ->
  temp_agree(pointer::expression_temps index)before current ->
  word_address_evaluate current pointer index=word_address_evaluate before pointer index.
Proof.
  intros WORD FRAME; unfold word_address_evaluate.
  rewrite FRAME by(left; reflexivity).
  rewrite(@word_evaluate_frame index WORD before current); [reflexivity|].
  intros id MEMBER; apply FRAME; right; exact MEMBER.
Qed.

Definition renamed_word_frame rename pointer index before current :=
  before!pointer=current!pointer /\ word_rename_frame rename index before current.
Theorem renamed_word_address_transport rename pointer index ge locals before memory current target_memory block offset :
  word_arithmetic index -> renamed_word_frame rename pointer index before current ->
  eval_expr ge locals before memory(direct_word_address pointer index)(Vptr block offset) ->
  eval_expr ge locals current target_memory(direct_word_address pointer(word_rename rename index))(Vptr block offset).
Proof.
  intros WORD [POINTER FRAME] SOURCE.
  destruct(direct_word_address_operands WORD SOURCE)as [base [word [PTR [INDEX OP]]]].
  eapply eval_Ebinop; [apply eval_Etempvar; rewrite <-POINTER; exact PTR|
    eapply word_rename_evaluation; eassumption|].
  rewrite word_rename_type,(word_arithmetic_type WORD); exact OP.
Qed.

Print Assumptions word_rename_type.
Print Assumptions word_rename_arithmetic.
Print Assumptions word_rename_temps.
Print Assumptions word_rename_evaluation.
Print Assumptions word_evaluate_sound.
Print Assumptions word_evaluate_complete.
Print Assumptions word_evaluate_frame.
Print Assumptions word_address_evaluate_complete.
Print Assumptions word_address_evaluate_sound.
Print Assumptions word_address_evaluate_frame.
Print Assumptions renamed_word_address_transport.
