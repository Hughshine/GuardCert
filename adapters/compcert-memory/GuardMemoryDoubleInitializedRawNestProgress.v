From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Ctypes Clight.
From Guard Require Import SilentRegionProtocol ClightRegionProgress ClightFragmentProgress ClightSequenceProgress.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryDoubleAssignmentFactory
  GuardMemoryDoubleSourceInstruction GuardMemoryDoubleInitializedReductionData GuardMemoryDoubleInitializedNestData
  GuardMemoryLongRawLoadedProgress GuardMemoryLongLoopControl GuardMemoryDoubleMatmulLoops
  GuardMemoryDoubleInitializedNestProgress GuardMemoryDoubleInitializedRawNest.
Import ListNotations.
Set Implicit Arguments.

Lemma double_initialized_raw_nest_assignment_progress outers description :
  (exists target rhs, initialized_reduction_initializer description=Sassign target rhs) ->
  (exists target rhs, initialized_reduction_body description=Sassign target rhs) ->
  forall protected, NoDup (outers++[initialized_reduction_iterator description]) ->
    (forall key, In key protected -> ~ In key (outers++[initialized_reduction_iterator description])) ->
    exists F : framed_progress (double_initialized_raw_nest_code outers description) protected, True.
Proof.
  intros [initial_target [initial_rhs INITIAL]] [target [rhs BODY]].
  induction outers as [|iterator rest IH]; intros protected NODUP DISJOINT.
  - assert (INITIAL_F : framed_progress (Ssequence Sskip (initialized_reduction_initializer description)) protected).
    { rewrite INITIAL; apply finite_framed_progress; reflexivity. }
    assert (BODY_F : framed_progress (Ssequence Sskip (initialized_reduction_body description))
      (initialized_reduction_iterator description::protected)).
    { rewrite BODY; apply finite_framed_progress; reflexivity. }
    assert (FRESH : ~ In (initialized_reduction_iterator description) protected).
    { intro MEMBER; apply (DISJOINT _ MEMBER); cbn; auto. }
    exists (@sequence_framed_progress (Ssequence Sskip (initialized_reduction_initializer description))
      (long_raw_initialized_loop (initialized_reduction_iterator description)
        (Evar (initialized_reduction_header description) memory_long_type) (Ssequence Sskip (initialized_reduction_body description)))
      protected INITIAL_F (@long_raw_initialized_framed_progress (initialized_reduction_iterator description)
        (Evar (initialized_reduction_header description) memory_long_type) eq_refl protected FRESH
        (Ssequence Sskip (initialized_reduction_body description)) BODY_F)); exact I.
  - cbn [app] in NODUP; inversion NODUP as [|key keys FRESH REST]; subst key keys.
    assert (CHILD_DISJOINT : forall key, In key (iterator::protected) ->
      ~ In key (rest++[initialized_reduction_iterator description])).
    { intros key MEMBER; cbn in MEMBER; destruct MEMBER as [SAME|MEMBER]; [subst; exact FRESH|].
      intro WRITTEN; apply (DISJOINT key MEMBER); cbn; auto. }
    destruct (@IH (iterator::protected) REST CHILD_DISJOINT) as [BODY_F TRIVIAL].
    assert (NOT_PROTECTED : ~ In iterator protected).
    { intro MEMBER; apply (DISJOINT iterator MEMBER); cbn; auto. }
    exists (@long_raw_initialized_framed_progress iterator
      (Evar (initialized_reduction_header description) memory_long_type) eq_refl protected NOT_PROTECTED
      (double_initialized_raw_nest_code rest description) BODY_F); exact I.
Qed.
Theorem checked_double_initialized_raw_nest_framed_progress p controls source outers description protected :
  checked_double_initialized_raw_nest p controls source=Some (outers,description) ->
  (forall key, In key protected -> ~ In key (outers++[initialized_reduction_iterator description])) ->
  exists F : framed_progress source protected, True.
Proof.
  intros CHECK DISJOINT.
  destruct (@checked_double_initialized_raw_nest_sound p controls source outers description CHECK) as [CODE [CANONICAL EQUIV]].
  destruct (@checked_double_initialized_nest_sound p controls (double_initialized_nest_code outers description)
    outers description CANONICAL) as [TRIVIAL [LEAF FRESH]].
  destruct (@checked_double_initialized_reduction_sound p (controls++outers)
    (double_initialized_reduction_code description) description LEAF) as [_ [IC [BC STATIC]]].
  destruct (@double_initialized_reduction_static_sound p (controls++outers) description STATIC) as [DISTINCT REST].
  destruct (@checked_double_source_instruction_sound p (controls++outers) (initialized_reduction_initializer description)
    (initialized_reduction_initial_instruction description) IC) as [IDEC _].
  destruct (@checked_double_source_instruction_sound p ((controls++outers)++[initialized_reduction_iterator description])
    (initialized_reduction_body description) (initialized_reduction_body_instruction description) BC) as [BDEC _].
  destruct (@decoded_double_assignment_shape (initialized_reduction_initializer description)
    (double_source_assignment (initialized_reduction_initial_instruction description)) IDEC) as [initial_rhs [INITIAL TYPE]].
  destruct (@decoded_double_assignment_shape (initialized_reduction_body description)
    (double_source_assignment (initialized_reduction_body_instruction description)) BDEC) as [rhs [BODY TYPE']].
  rewrite CODE; apply double_initialized_raw_nest_assignment_progress.
  - eexists; eexists; exact INITIAL.
  - eexists; eexists; exact BODY.
  - apply double_initialized_nest_nodup_snoc; [eapply double_initialized_nest_fresh_nodup; exact FRESH|].
    intro MEMBER; apply DISTINCT; apply in_or_app; auto.
  - exact DISJOINT.
Qed.
Theorem checked_double_initialized_raw_nest_region_progress p controls source outers description :
  checked_double_initialized_raw_nest p controls source=Some (outers,description) -> exists F : region_progress source, True.
Proof.
  intro CHECK; destruct (@checked_double_initialized_raw_nest_framed_progress p controls source outers description []
    CHECK ltac:(intros key MEMBER; contradiction)) as [F TRIVIAL].
  assert (NOT_SKIP : source<>Sskip).
  { destruct (@checked_double_initialized_raw_nest_sound p controls source outers description CHECK) as [CODE REST].
    rewrite CODE; destruct outers; cbn [double_initialized_raw_nest_code];
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

Print Assumptions double_initialized_raw_nest_assignment_progress.
Print Assumptions checked_double_initialized_raw_nest_framed_progress.
Print Assumptions checked_double_initialized_raw_nest_region_progress.
