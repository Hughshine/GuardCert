From Stdlib Require Import List Bool.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightSyntaxEquality ClightRegionProgress ClightFragmentProgress
  ClightSequenceProgress ClightStructuredProgress ClightNestedProgress ClightNestedFrontendProgress.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightStrictNestedProgress
  ClightSequenceProgressSelector.
Import ListNotations.
Set Implicit Arguments.

(** This describes source progress, independently of a rewrite's condition.
    An exact syntax check binds each proposed loaded loop to its protocol. *)
Definition propose_loaded_progress source :=
  match source with
  | Sloop (Ssequence (Ssequence Sskip (Sifthenelse
      (Ebinop Olt (Etempvar iterator _) (Ederef (Etempvar pointer _) _) _) Sskip Sbreak)) body) _ =>
    Some (iterator, pointer, body)
  | _ => None end.
Definition checked_loaded_progress source :=
  match propose_loaded_progress source with
  | Some (iterator, pointer, body) =>
    if statement_eq source (loaded_bound_loop iterator pointer body)
    then Some (iterator, pointer, body) else None
  | None => None end.
Lemma checked_loaded_progress_binds source iterator pointer body :
  checked_loaded_progress source = Some (iterator, pointer, body) ->
  source = loaded_bound_loop iterator pointer body.
Proof.
  unfold checked_loaded_progress.
  destruct (propose_loaded_progress source) as [[[i p] b]|]; try discriminate.
  destruct (statement_eq source (loaded_bound_loop i p b)) as [EQ|]; try discriminate.
  intro SELECT; inversion SELECT; subst; reflexivity.
Qed.

Fixpoint loaded_framed_supported (fuel : nat) protected source : bool :=
  match fuel with
  | O => false
  | S rest =>
    if frame_statement protected source then true else
    match sequence_parts source with
    | Some (first,second) => loaded_framed_supported rest protected first &&
        loaded_framed_supported rest protected second
    | None => match checked_structured_loop source with
      | Some d =>
        if peq (described_iterator d) (described_bound d) then false else
        if in_dec peq (described_iterator d) protected then false else
        loaded_framed_supported rest
          (described_iterator d :: described_bound d :: protected) (described_body d)
      | None => match checked_loaded_progress source with
        | Some (iterator, pointer, body) =>
          if in_dec peq iterator protected then false else
          loaded_framed_supported rest (iterator :: protected) body
        | None => false end end end end.

Theorem loaded_framed_supported_sound fuel protected source :
  loaded_framed_supported fuel protected source = true ->
  exists MODEL : framed_progress source protected, True.
Proof.
  revert protected source; induction fuel as [|fuel IH]; intros protected source; [discriminate|].
  cbn [loaded_framed_supported].
  destruct (frame_statement protected source) eqn:FINITE.
  - intros _; exists (finite_framed_progress protected source FINITE); exact I.
  - destruct (sequence_parts source) as [[first second]|] eqn:PARTS.
    + rewrite andb_true_iff; intros [LEFT RIGHT].
      destruct (IH protected first LEFT) as [F _], (IH protected second RIGHT) as [G _].
      apply sequence_parts_binds in PARTS; subst source.
      exists (sequence_framed_progress F G); exact I.
    + destruct (checked_structured_loop source) as [d|] eqn:CACHED.
      * destruct (peq (described_iterator d) (described_bound d)) as [EQ|DISTINCT]; try discriminate.
        destruct (in_dec peq (described_iterator d) protected) as [IN|NOT_WRITTEN]; try discriminate.
        intro BODY; destruct (IH _ _ BODY) as [F _].
        apply checked_structured_loop_binds in CACHED; subst source.
        destruct d as [iterator bound body frontend]; cbn in DISTINCT, NOT_WRITTEN, F |- *.
        unfold described_loop; cbn; destruct frontend.
        -- exists (@frontend_framed_progress iterator bound DISTINCT protected NOT_WRITTEN body F); exact I.
        -- exists (@counted_framed_progress iterator bound DISTINCT protected NOT_WRITTEN body F); exact I.
      * destruct (checked_loaded_progress source) as [[[iterator pointer] body]|] eqn:LOADED; try discriminate.
        destruct (in_dec peq iterator protected) as [IN|NOT_WRITTEN]; try discriminate.
        intro BODY; destruct (IH _ _ BODY) as [F _].
        apply checked_loaded_progress_binds in LOADED; subst source.
        exists (@strict_nested_framed_progress iterator (loaded_bound_test iterator pointer)
          protected NOT_WRITTEN body F
          (fun ge locals le memory => @loaded_bound_test_strict ge locals le memory iterator pointer)); exact I.
Qed.

Definition loaded_sequence_progress_supported source :=
  match source with
  | Ssequence first second =>
    loaded_framed_supported (progress_syntax_size source) [] first &&
    loaded_framed_supported (progress_syntax_size source) [] second
  | _ => match checked_loaded_progress source with
    | Some (iterator, pointer, body) =>
      loaded_framed_supported (progress_syntax_size source) [iterator] body
    | None => sequence_progress_supported source end end.

Theorem loaded_sequence_progress_supported_sound source :
  loaded_sequence_progress_supported source = true ->
  exists MODEL : region_progress source, True.
Proof.
  unfold loaded_sequence_progress_supported.
  destruct source; try match goal with
    |- context [checked_loaded_progress ?s] =>
      destruct (checked_loaded_progress s) as [[[iterator pointer] body]|] eqn:LOADED
    end; try apply sequence_progress_supported_sound.
  all: try solve [
    intro BODY; destruct (loaded_framed_supported_sound _ _ _ BODY) as [F _];
    apply checked_loaded_progress_binds in LOADED;
    rewrite LOADED;
    exists (@strict_nested_region_progress iterator (loaded_bound_test iterator pointer) body F
      (fun ge locals le memory => @loaded_bound_test_strict ge locals le memory iterator pointer)); exact I].
  rewrite andb_true_iff; intros [FIRST SECOND].
  destruct (loaded_framed_supported_sound _ _ _ FIRST) as [F _],
    (loaded_framed_supported_sound _ _ _ SECOND) as [G _].
  exists (sequence_region_progress F G); exact I.
Qed.

Print Assumptions checked_loaded_progress_binds.
Print Assumptions loaded_framed_supported_sound.
Print Assumptions loaded_sequence_progress_supported_sound.
