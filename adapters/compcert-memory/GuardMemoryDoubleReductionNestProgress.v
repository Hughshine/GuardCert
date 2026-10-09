From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Ctypes Clight.
From Guard Require Import SilentRegionProtocol ClightRegionProgress ClightFragmentProgress ClightSequenceProgress.
From GuardMemory Require Import GuardMemoryDoubleReductionNestData GuardMemoryDoubleReductionNestSource
  GuardMemoryDoubleInitializedNestData GuardMemoryLongRawLoadedProgress GuardMemoryDoubleLocations.
Import ListNotations.
Set Implicit Arguments.

Lemma double_reduction_raw_nest_assignment_progress iterators header body :
  (exists target rhs, body=Sassign target rhs) -> forall protected,
  NoDup iterators -> (forall key, In key protected -> ~ In key iterators) ->
  exists F : framed_progress (double_reduction_raw_nest_code iterators header body) protected, True.
Proof.
  intros [target [rhs BODY]]; induction iterators as [|iterator rest IH]; intros protected NODUP DISJOINT.
  - cbn [double_reduction_raw_nest_code]; rewrite BODY.
    assert (F : framed_progress (Ssequence Sskip (Sassign target rhs)) protected)
      by (apply finite_framed_progress; reflexivity).
    exists F; exact I.
  - inversion NODUP as [|key keys FRESH REST]; subst key keys.
    assert (CHILD_DISJOINT : forall key, In key (iterator::protected) -> ~ In key rest).
    { intros key MEMBER; cbn in MEMBER; destruct MEMBER as [SAME|MEMBER]; [subst; exact FRESH|].
      intro WRITTEN; apply (DISJOINT key MEMBER); cbn; auto. }
    destruct (@IH (iterator::protected) REST CHILD_DISJOINT) as [BODY_F TRIVIAL].
    assert (NOT_PROTECTED : ~ In iterator protected).
    { intro MEMBER; apply (DISJOINT iterator MEMBER); cbn; auto. }
    exists (@long_raw_initialized_framed_progress iterator (Evar header memory_long_type) eq_refl
      protected NOT_PROTECTED (double_reduction_raw_nest_code rest header body) BODY_F); exact I.
Qed.
Theorem checked_double_reduction_raw_nest_framed_progress p controls source description protected :
  checked_double_reduction_raw_nest p controls source=Some description ->
  (forall key, In key protected -> ~ In key (reduction_nest_iterators description)) ->
  exists F : framed_progress source protected, True.
Proof.
  intros CHECK DISJOINT.
  destruct (@checked_double_reduction_raw_nest_sound p controls source description CHECK) as [CODE [CANONICAL EQUIV]].
  destruct (@checked_double_reduction_nest_sound p controls _ description CANONICAL) as [_ [LEAF [FRESH REST]]].
  rewrite CODE; apply double_reduction_raw_nest_assignment_progress.
  - eapply checked_double_reduction_assignment_shape; exact LEAF.
  - eapply double_initialized_nest_fresh_nodup; exact FRESH.
  - exact DISJOINT.
Qed.
Theorem checked_double_reduction_raw_nest_region_progress p controls source description :
  checked_double_reduction_raw_nest p controls source=Some description -> exists F : region_progress source, True.
Proof.
  intro CHECK; destruct (@checked_double_reduction_raw_nest_framed_progress p controls source description []
    CHECK ltac:(intros key MEMBER; contradiction)) as [F TRIVIAL].
  assert (NOT_SKIP : source<>Sskip).
  { destruct (@checked_double_reduction_raw_nest_sound p controls source description CHECK) as [CODE REST].
    rewrite CODE; destruct (reduction_nest_iterators description); cbn [double_reduction_raw_nest_code];
      unfold long_raw_initialized_loop; discriminate. }
  assert (START : forall temps ge fn outside locals input,
    cursor_done (framed_protocol F temps ge fn outside locals)
      (begin_cursor (framed_entry F temps ge fn outside locals) input)=None).
  { intros temps ge fn outside locals input.
    destruct (cursor_done (framed_protocol F temps ge fn outside locals)
      (begin_cursor (framed_entry F temps ge fn outside locals) input)) as [result|] eqn:DONE; [|reflexivity].
    pose proof (cursor_done_state (framed_protocol F temps ge fn outside locals) _ DONE) as SAME.
    rewrite (begin_state (framed_entry F temps ge fn outside locals) input) in SAME.
    unfold progress_exit_state in SAME; inversion SAME; contradiction. }
  exists (@framed_region_progress source [] F START); exact I.
Qed.

Print Assumptions double_reduction_raw_nest_assignment_progress.
Print Assumptions checked_double_reduction_raw_nest_framed_progress.
Print Assumptions checked_double_reduction_raw_nest_region_progress.
