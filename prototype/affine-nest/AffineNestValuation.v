From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightTempFrame.
From GuardMemory Require Import GuardMemoryAffineSourceValuation GuardMemoryLoops.
Import ListNotations.
Set Implicit Arguments.

Definition affine_word_view registers valuation temps :=
  forall identifier, In identifier registers ->
    temps!identifier=Some(Vint(Int.repr(valuation identifier))).

Lemma affine_word_view_frame registers valuation before after :
  affine_word_view registers valuation before -> temp_agree registers before after ->
  affine_word_view registers valuation after.
Proof. intros WORDS FRAME identifier MEMBER; rewrite FRAME by exact MEMBER; apply WORDS; exact MEMBER. Qed.

Lemma affine_word_view_update registers valuation temps iterator value :
  affine_word_view registers valuation temps ->
  temps!iterator=Some(Vint(Int.repr value)) ->
  affine_word_view (registers++[iterator]) (memory_source_set_valuation valuation iterator value) temps.
Proof.
  intros WORDS ITERATOR identifier MEMBER; unfold memory_source_set_valuation.
  destruct (peq identifier iterator) as [->|OTHER]; [exact ITERATOR|].
  apply WORDS; apply in_app_or in MEMBER; destruct MEMBER as [MEMBER|MEMBER]; [exact MEMBER|].
  cbn in MEMBER; intuition congruence.
Qed.

Lemma affine_valuation_update_map registers valuation iterator value :
  ~In iterator registers ->
  map (memory_source_set_valuation valuation iterator value) registers=map valuation registers.
Proof.
  intro FRESH; apply map_ext_in; intros identifier MEMBER; unfold memory_source_set_valuation.
  destruct (peq identifier iterator); [subst; contradiction|reflexivity].
Qed.

Lemma affine_valuation_loop_environment prefix parameters tail valuation iterator value :
  ~In iterator (prefix++parameters) ->
  map (memory_source_set_valuation valuation iterator value) (rev(prefix++[iterator])++parameters)++tail =
  value::(map valuation (rev prefix++parameters)++tail).
Proof.
  intro FRESH; rewrite rev_app_distr; cbn [rev app map].
  unfold memory_source_set_valuation at 1; destruct (peq iterator iterator); [|contradiction].
  f_equal; rewrite affine_valuation_update_map; [reflexivity|].
  rewrite in_app_iff,<-in_rev; rewrite in_app_iff in FRESH; exact FRESH.
Qed.
Print Assumptions affine_word_view_frame.
Print Assumptions affine_word_view_update.
Print Assumptions affine_valuation_loop_environment.
