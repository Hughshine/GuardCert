From Stdlib Require Import List Bool Arith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightGuard ClightCondition ClightSyntaxEquality ClightRegionProgress
  ClightFrontendLoopProtocol ClightFragmentProgress ClightSequenceProgress ClightStructuredProgress
  ClightNestedProgress ClightNestedFrontendProgress.
From GuardInterface Require Import ClightStrictLoopProgress ClightNestedStrictProgress
  ClightLoadedBoundSyntax ClightLoadedBoundCompiler.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope nat_scope.

Definition checked_loaded_progress_loop source :=
  match propose_loaded_bound source with
  | Some (iterator,bound,body) => if statement_eq source (loaded_bound_loop iterator bound body)
      then Some (iterator,bound,body) else None
  | None => None end.
Lemma checked_loaded_progress_loop_binds source iterator bound body :
  checked_loaded_progress_loop source = Some (iterator,bound,body) -> source = loaded_bound_loop iterator bound body.
Proof.
  unfold checked_loaded_progress_loop; destruct (propose_loaded_bound source) as [[[i n] code]|]; try discriminate.
  destruct (statement_eq source (loaded_bound_loop i n code)) as [SAME|]; try discriminate.
  intro SELECT; inversion SELECT; subst; reflexivity.
Qed.

(** Memory-bound loops protect only their counter. Their loaded target may
    change after stores; strict signed maximum gives an independent rank.
    Register-bound loops retain the existing stable-bound protocol. *)
Fixpoint mixed_loaded_framed_supported (fuel : nat) protected source : bool :=
  match fuel with 0 => false | S rest =>
    if frame_statement protected source then true else
    match sequence_parts source with
    | Some (first,second) => mixed_loaded_framed_supported rest protected first &&
        mixed_loaded_framed_supported rest protected second
    | None => match checked_loaded_progress_loop source with
      | Some (iterator,bound,body) => if in_dec peq iterator protected then false else
          mixed_loaded_framed_supported rest (iterator::protected) body
      | None => match checked_structured_loop source with
        | Some d => if peq (described_iterator d) (described_bound d) then false else
            if in_dec peq (described_iterator d) protected then false else
            mixed_loaded_framed_supported rest (described_iterator d::described_bound d::protected) (described_body d)
        | None => false end end end end.

Theorem mixed_loaded_framed_supported_sound fuel protected source :
  mixed_loaded_framed_supported fuel protected source = true -> exists MODEL : framed_progress source protected, True.
Proof.
  revert protected source; induction fuel as [|fuel IH]; intros protected source; [discriminate|].
  cbn [mixed_loaded_framed_supported]; destruct (frame_statement protected source) eqn:FINITE.
  - intros _; exists (finite_framed_progress protected source FINITE); exact I.
  - destruct (sequence_parts source) as [[first second]|] eqn:PARTS.
    + rewrite andb_true_iff; intros [LEFT RIGHT].
      destruct (IH protected first LEFT) as [F _], (IH protected second RIGHT) as [G _].
      apply sequence_parts_binds in PARTS; subst source; exists (sequence_framed_progress F G); exact I.
    + destruct (checked_loaded_progress_loop source) as [[[iterator bound] body]|] eqn:LOADED.
      * destruct (in_dec peq iterator protected) as [IN|NOT_WRITTEN]; try discriminate.
        intro BODY; destruct (IH _ _ BODY) as [F _].
        apply checked_loaded_progress_loop_binds in LOADED; subst source.
        exists (@strict_framed_progress iterator (loaded_bound_test iterator bound)
          (fun ge locals le memory => @loaded_bound_test_strict ge locals le memory iterator bound)
          protected NOT_WRITTEN body F); exact I.
      * destruct (checked_structured_loop source) as [d|] eqn:LOOP; try discriminate.
        destruct (peq (described_iterator d) (described_bound d)) as [EQ|DISTINCT]; try discriminate.
        destruct (in_dec peq (described_iterator d) protected) as [IN|NOT_WRITTEN]; try discriminate.
        intro BODY; destruct (IH _ _ BODY) as [F _].
        apply checked_structured_loop_binds in LOOP; subst source.
        destruct d as [iterator bound body frontend]; cbn in DISTINCT, NOT_WRITTEN, F |- *.
        unfold described_loop; cbn; destruct frontend.
        -- exists (@frontend_framed_progress iterator bound DISTINCT protected NOT_WRITTEN body F); exact I.
        -- exists (@counted_framed_progress iterator bound DISTINCT protected NOT_WRITTEN body F); exact I.
Qed.
Definition mixed_loaded_progress_supported source :=
  match checked_loaded_progress_loop source with
  | Some (iterator,bound,body) => mixed_loaded_framed_supported (progress_syntax_size body) [iterator] body
  | None => structured_progress_supported source end.
Theorem mixed_loaded_progress_supported_sound source : mixed_loaded_progress_supported source = true ->
  exists MODEL : region_progress source, True.
Proof.
  unfold mixed_loaded_progress_supported; destruct (checked_loaded_progress_loop source) as [[[iterator bound] body]|] eqn:LOOP.
  - intro SUPPORTED; destruct (mixed_loaded_framed_supported_sound _ _ _ SUPPORTED) as [F _].
    apply checked_loaded_progress_loop_binds in LOOP; subst source.
    exists (@strict_nested_region_progress iterator (loaded_bound_test iterator bound)
      (fun ge locals le memory => @loaded_bound_test_strict ge locals le memory iterator bound)
      [] (fun BAD => BAD) body F); exact I.
  - apply structured_progress_supported_sound.
Qed.

Print Assumptions checked_loaded_progress_loop_binds.
Print Assumptions mixed_loaded_framed_supported_sound.
Print Assumptions mixed_loaded_progress_supported_sound.
