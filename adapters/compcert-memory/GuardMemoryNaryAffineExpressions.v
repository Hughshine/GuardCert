From Stdlib Require Import List ZArith Lia Bool.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import Linalg.
From Guard Require Import ClightRectangularStore.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceLoop.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint memory_nary_unit dimensions position : list Z :=
  match dimensions,position with
  | O,_ => []
  | S rest,O => 1::repeat 0 rest
  | S rest,S index => 0::memory_nary_unit rest index
  end.
Lemma memory_nary_unit_value values position :
  dot_product (memory_nary_unit (length values) position) values = nth position values 0.
Proof.
  revert position; induction values as [|value rest IH]; intros [|position]; cbn; auto.
  - rewrite dot_product_repeat_zero_left; ring.
Qed.
Fixpoint memory_encode_nary_index (layout : list ident) expression : option constraint :=
  match expression with
  | MemorySourceTemp identifier => option_map (fun position => (memory_nary_unit (length layout) position,0))
      (memory_source_position identifier layout)
  | MemorySourceConstant value => Some (repeat 0 (length layout),value)
  | MemorySourceAdd first second | MemorySourceSub first second =>
      match memory_encode_nary_index layout first,memory_encode_nary_index layout second with
      | Some first,Some second => Some (add_constraint first
          (match expression with MemorySourceSub _ _ => mult_constraint (-1) second | _ => second end))
      | _,_ => None end
  | MemorySourceScale factor value | MemorySourceScaleLeft factor value =>
      option_map (mult_constraint factor) (memory_encode_nary_index layout value)
  end.
Definition memory_nary_index_value term values := dot_product (fst term) values+snd term.
Lemma memory_encode_nary_index_value expression (layout : list ident) term valuation :
  memory_encode_nary_index layout expression = Some term ->
  memory_source_affine_math valuation expression = memory_nary_index_value term (map valuation layout).
Proof.
  revert term; induction expression; intros term ENCODE; cbn [memory_encode_nary_index] in ENCODE.
  - destruct (memory_source_position identifier layout) as [position|] eqn:POSITION; cbn in ENCODE; [|discriminate].
    inversion ENCODE; subst term; unfold memory_nary_index_value; cbn [fst snd memory_source_affine_math].
    replace (length layout) with (length (map valuation layout)) by apply length_map.
    rewrite memory_nary_unit_value.
    rewrite <- (@memory_source_position_value identifier layout position valuation POSITION).
    apply eq_sym, Z.add_0_r.
  - inversion ENCODE; subst term; unfold memory_nary_index_value; cbn [fst snd memory_source_affine_math].
    rewrite dot_product_repeat_zero_left; ring.
  - destruct (memory_encode_nary_index layout expression1) as [first|] eqn:FIRST; [|discriminate].
    destruct (memory_encode_nary_index layout expression2) as [second|] eqn:SECOND; [|discriminate].
    inversion ENCODE; subst term; cbn [memory_source_affine_math].
    rewrite (IHexpression1 _ eq_refl),(IHexpression2 _ eq_refl).
    unfold memory_nary_index_value,add_constraint; cbn [fst snd].
    rewrite add_vector_dot_product_distr_left; ring.
  - destruct (memory_encode_nary_index layout expression1) as [first|] eqn:FIRST; [|discriminate].
    destruct (memory_encode_nary_index layout expression2) as [second|] eqn:SECOND; [|discriminate].
    inversion ENCODE; subst term; cbn [memory_source_affine_math].
    rewrite (IHexpression1 _ eq_refl),(IHexpression2 _ eq_refl).
    unfold memory_nary_index_value,add_constraint,mult_constraint; cbn [fst snd].
    rewrite add_vector_dot_product_distr_left,dot_product_mult_left; ring.
  - destruct (memory_encode_nary_index layout expression) as [first|] eqn:FIRST; cbn in ENCODE; [|discriminate].
    inversion ENCODE; subst term; cbn [memory_source_affine_math]; rewrite (IHexpression _ eq_refl).
    unfold memory_nary_index_value,mult_constraint; cbn [fst snd]; rewrite dot_product_mult_left; ring.
  - destruct (memory_encode_nary_index layout expression) as [first|] eqn:FIRST; cbn in ENCODE; [|discriminate].
    inversion ENCODE; subst term; cbn [memory_source_affine_math]; rewrite (IHexpression _ eq_refl).
    unfold memory_nary_index_value,mult_constraint; cbn [fst snd]; rewrite dot_product_mult_left; ring.
Qed.
Lemma memory_source_position_member identifier layout position :
  memory_source_position identifier layout = Some position -> In identifier layout.
Proof.
  revert position; induction layout as [|first rest IH]; intros position LOOKUP; cbn in LOOKUP; [discriminate|].
  destruct (peq identifier first) as [->|OTHER]; [cbn; auto|].
  destruct (memory_source_position identifier rest) as [index|] eqn:INDEX; cbn in LOOKUP; [|discriminate].
  right; eapply IH; reflexivity.
Qed.
Lemma memory_encode_nary_index_reads expression (layout : list ident) term :
  memory_encode_nary_index layout expression = Some term ->
  forall identifier, In identifier (memory_source_affine_reads expression) -> In identifier layout.
Proof.
  revert term; induction expression; intros term ENCODE read MEMBER; cbn [memory_encode_nary_index] in ENCODE.
  - cbn in MEMBER; destruct MEMBER as [<-|[]].
    destruct (memory_source_position identifier layout) as [position|] eqn:POSITION; cbn in ENCODE; [|discriminate].
    eapply memory_source_position_member; exact POSITION.
  - contradiction.
  - destruct (memory_encode_nary_index layout expression1) as [first|] eqn:FIRST; [|discriminate].
    destruct (memory_encode_nary_index layout expression2) as [second|] eqn:SECOND; [|discriminate].
    apply in_app_or in MEMBER as [MEMBER|MEMBER]; [eapply IHexpression1|eapply IHexpression2]; eauto.
  - destruct (memory_encode_nary_index layout expression1) as [first|] eqn:FIRST; [|discriminate].
    destruct (memory_encode_nary_index layout expression2) as [second|] eqn:SECOND; [|discriminate].
    apply in_app_or in MEMBER as [MEMBER|MEMBER]; [eapply IHexpression1|eapply IHexpression2]; eauto.
  - destruct (memory_encode_nary_index layout expression) as [first|] eqn:FIRST; [|discriminate].
    eapply IHexpression; eauto.
  - destruct (memory_encode_nary_index layout expression) as [first|] eqn:FIRST; [|discriminate].
    eapply IHexpression; eauto.
Qed.
Theorem memory_nary_index_expression_evaluation expression (layout : list ident) term valuation ge locals temps memory :
  memory_encode_nary_index layout expression = Some term ->
  (forall identifier, In identifier layout -> temps ! identifier = Some (Vint (Int.repr (valuation identifier)))) ->
  eval_expr ge locals temps memory (memory_source_affine_code expression)
    (Vint (Int.repr (memory_nary_index_value term (map valuation layout)))).
Proof.
  intros ENCODE WORDS.
  replace (memory_nary_index_value term (map valuation layout)) with (memory_source_affine_math valuation expression)
    by exact (@memory_encode_nary_index_value expression (layout : list ident) term valuation ENCODE).
  apply memory_source_affine_evaluation; intros identifier MEMBER; apply WORDS.
  eapply memory_encode_nary_index_reads; eassumption.
Qed.
Print Assumptions memory_encode_nary_index_value.
Print Assumptions memory_nary_index_expression_evaluation.
