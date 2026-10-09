From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Ctypes Clight.
From Guard Require Import SilentRegionProtocol ClightRegionProgress ClightFragmentProgress ClightSequenceProgress.
From GuardMemory Require Import GuardMemoryDoubleReductionNestData GuardMemoryDoubleReductionNestSource
  GuardMemoryDoubleInitializedNestData GuardMemoryLongRawLoadedProgress GuardMemoryDoubleLocations
  GuardMemoryDoubleReductionNestProgress GuardMemoryDoubleHeaderNestData GuardMemoryDoubleHeaderNestSource.
Import ListNotations.
Set Implicit Arguments.

Theorem checked_double_header_raw_nest_framed_progress p controls source description protected :
  checked_double_header_raw_nest p controls source=Some description ->
  (forall key, In key protected -> ~ In key (reduction_nest_iterators description)) ->
  exists F : framed_progress source protected, True.
Proof.
  intros CHECK DISJOINT.
  destruct (@checked_double_header_raw_nest_sound p controls source description CHECK) as [CODE [CANONICAL EQUIV]].
  destruct (@checked_double_header_nest_sound p controls _ description CANONICAL) as [_ [LEAF [FRESH REST]]].
  rewrite CODE; apply double_reduction_raw_nest_assignment_progress.
  - eapply checked_double_header_assignment_shape; exact LEAF.
  - eapply double_initialized_nest_fresh_nodup; exact FRESH.
  - exact DISJOINT.
Qed.
Theorem checked_double_header_raw_nest_region_progress p controls source description :
  checked_double_header_raw_nest p controls source=Some description -> exists F : region_progress source, True.
Proof.
  intro CHECK; destruct (@checked_double_header_raw_nest_framed_progress p controls source description []
    CHECK ltac:(intros key MEMBER; contradiction)) as [F TRIVIAL].
  assert (NOT_SKIP : source<>Sskip).
  { destruct (@checked_double_header_raw_nest_sound p controls source description CHECK) as [CODE REST].
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


Print Assumptions checked_double_header_raw_nest_framed_progress.
Print Assumptions checked_double_header_raw_nest_region_progress.
