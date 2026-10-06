From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Integers.
From compcert.common Require Import AST Values.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightSyntaxEquality ClightPureExpr ClightNoWrap ClightCondition ClightRegionProgress
  ClightFragmentProgress ClightSequenceProgress ClightStructuredProgress ClightNestedProgress ClightNestedFrontendProgress.
From GuardInterface Require Import ClightStrictLoopProgress ClightStrictNestedProgress ClightSequenceProgressSelector.
Import ListNotations.
Set Implicit Arguments.

(** Source progress needs signed comparison, not a fixed loaded bound.
    The expression may include dependent reads; undefined evaluation can get
    stuck, while a successful header still gives a strict machine counter. *)
Definition signed_expression_test iterator bound :=
  Ebinop Olt (Etempvar iterator type_int32s) bound type_int32s.
Lemma signed_expression_test_strict ge locals temps memory iterator bound :
  typeof bound = type_int32s ->
  expression_test (signed_expression_test iterator bound) (Entry ge locals temps memory) true ->
  strict_counter_active iterator temps.
Proof.
  intros TYPE [result [EVAL BOOL]]; apply scalar_binary_inv in EVAL.
  destruct EVAL as [counter [upper [ROW [BOUND OP]]]]; apply scalar_temp_inv in ROW.
  unfold Cop.sem_binary_operation in OP; cbn [typeof] in OP; rewrite TYPE in OP.
  destruct counter; destruct upper; try discriminate OP.
  change (Some (Val.of_bool (Int.lt i i0)) = Some result) in OP; injection OP as VALUE; subst result.
  rewrite bool_of_bool in BOOL; exists i; split; [exact ROW|].
  unfold Int.lt in BOOL; destruct (zlt (Int.signed i) (Int.signed i0));
    [pose proof (Int.signed_range i0); lia|discriminate].
Qed.

Definition propose_signed_expression_progress source :=
  match source with
  | Sloop (Ssequence (Ssequence Sskip (Sifthenelse
      (Ebinop Olt (Etempvar iterator _) bound _) Sskip Sbreak)) body) _ => Some (iterator,bound,body)
  | _ => None end.
Definition checked_signed_expression_progress source :=
  match propose_signed_expression_progress source with
  | Some (iterator,bound,body) =>
    if type_eq (typeof bound) type_int32s then
      if statement_eq source (strict_frontend_loop iterator (signed_expression_test iterator bound) body)
      then Some (iterator,bound,body) else None
    else None
  | None => None end.
Lemma checked_signed_expression_progress_binds source iterator bound body :
  checked_signed_expression_progress source = Some (iterator,bound,body) ->
  source = strict_frontend_loop iterator (signed_expression_test iterator bound) body /\ typeof bound = type_int32s.
Proof.
  unfold checked_signed_expression_progress.
  destruct (propose_signed_expression_progress source) as [[[i b] code]|]; [|discriminate].
  destruct (type_eq (typeof b) type_int32s) as [TYPE|]; [|discriminate].
  destruct (statement_eq source (strict_frontend_loop i (signed_expression_test i b) code)) as [SOURCE|]; [|discriminate].
  intro SELECT; inversion SELECT; subst; auto.
Qed.

Fixpoint signed_expression_framed_supported (fuel : nat) protected source : bool :=
  match fuel with
  | O => false
  | S rest => if frame_statement protected source then true else
    match sequence_parts source with
    | Some (first,second) => signed_expression_framed_supported rest protected first &&
        signed_expression_framed_supported rest protected second
    | None => match checked_structured_loop source with
      | Some description =>
        if peq (described_iterator description) (described_bound description) then false else
        if in_dec peq (described_iterator description) protected then false else
        signed_expression_framed_supported rest
          (described_iterator description :: described_bound description :: protected) (described_body description)
      | None => match checked_signed_expression_progress source with
        | Some (iterator,bound,body) => if in_dec peq iterator protected then false else
          signed_expression_framed_supported rest (iterator::protected) body
        | None => false end end end end.

Theorem signed_expression_framed_supported_sound fuel protected source :
  signed_expression_framed_supported fuel protected source = true -> exists MODEL : framed_progress source protected, True.
Proof.
  revert protected source; induction fuel as [|fuel IH]; intros protected source; [discriminate|].
  cbn [signed_expression_framed_supported]; destruct (frame_statement protected source) eqn:FINITE.
  - intros _; exists (finite_framed_progress protected source FINITE); exact I.
  - destruct (sequence_parts source) as [[first second]|] eqn:PARTS.
    + rewrite andb_true_iff; intros [LEFT RIGHT].
      destruct (IH protected first LEFT) as [F _],(IH protected second RIGHT) as [G _].
      apply sequence_parts_binds in PARTS; subst source; exists (sequence_framed_progress F G); exact I.
    + destruct (checked_structured_loop source) as [description|] eqn:CACHED.
      * destruct (peq (described_iterator description) (described_bound description)) as [SAME|DISTINCT]; [discriminate|].
        destruct (in_dec peq (described_iterator description) protected) as [MEMBER|PRIVATE]; [discriminate|].
        intro BODY; destruct (IH _ _ BODY) as [F _]; apply checked_structured_loop_binds in CACHED; subst source.
        destruct description as [iterator bound body frontend]; cbn in DISTINCT,PRIVATE,F |- *.
        unfold described_loop; cbn; destruct frontend.
        -- exists (@frontend_framed_progress iterator bound DISTINCT protected PRIVATE body F); exact I.
        -- exists (@counted_framed_progress iterator bound DISTINCT protected PRIVATE body F); exact I.
      * destruct (checked_signed_expression_progress source) as [[[iterator bound] body]|] eqn:EXPRESSION; [|discriminate].
        destruct (in_dec peq iterator protected) as [MEMBER|PRIVATE]; [discriminate|].
        intro BODY; destruct (IH _ _ BODY) as [F _].
        destruct (@checked_signed_expression_progress_binds source iterator bound body EXPRESSION) as [SOURCE TYPE]; subst source.
        exists (@strict_nested_framed_progress iterator (signed_expression_test iterator bound) protected PRIVATE body F
          (fun ge locals temps memory => @signed_expression_test_strict ge locals temps memory iterator bound TYPE)); exact I.
Qed.

Definition signed_expression_region_progress_supported source :=
  match source with
  | Ssequence first second =>
    signed_expression_framed_supported (progress_syntax_size source) [] first &&
      signed_expression_framed_supported (progress_syntax_size source) [] second
  | _ => match checked_signed_expression_progress source with
    | Some (iterator,bound,body) => signed_expression_framed_supported (progress_syntax_size source) [iterator] body
    | None => sequence_progress_supported source end end.
Theorem signed_expression_region_progress_supported_sound source :
  signed_expression_region_progress_supported source = true -> exists MODEL : region_progress source, True.
Proof.
  unfold signed_expression_region_progress_supported.
  destruct source; try match goal with
    |- context [checked_signed_expression_progress ?source] =>
      destruct (checked_signed_expression_progress source) as [[[iterator bound] body]|] eqn:SELECT
    end; try apply sequence_progress_supported_sound.
  all: try solve [
    intro BODY; destruct (signed_expression_framed_supported_sound _ _ _ BODY) as [F _];
    destruct (@checked_signed_expression_progress_binds _ _ _ _ SELECT) as [SOURCE TYPE]; rewrite SOURCE;
    exists (@strict_nested_region_progress iterator (signed_expression_test iterator bound) body F
      (fun ge locals temps memory => @signed_expression_test_strict ge locals temps memory iterator bound TYPE)); exact I].
  rewrite andb_true_iff; intros [FIRST SECOND].
  destruct (signed_expression_framed_supported_sound _ _ _ FIRST) as [F _],
    (signed_expression_framed_supported_sound _ _ _ SECOND) as [G _].
  exists (sequence_region_progress F G); exact I.
Qed.

Print Assumptions signed_expression_test_strict.
Print Assumptions checked_signed_expression_progress_binds.
Print Assumptions signed_expression_framed_supported_sound.
Print Assumptions signed_expression_region_progress_supported_sound.
