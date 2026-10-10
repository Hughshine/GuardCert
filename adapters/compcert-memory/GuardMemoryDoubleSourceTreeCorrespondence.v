From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightRegionProgress.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryDoubleLocations
  GuardMemoryDoubleSourceInstruction GuardMemoryDoubleSourceTreeData GuardMemoryDoubleSourceTreeDecode
  GuardMemoryDoubleSourceTreeCertificates GuardMemoryDoubleSourceTreeState GuardMemoryDoubleSourceTreeSource
  GuardMemoryDoubleSourceTreeModelData GuardMemoryDoubleSourceLoopModel GuardMemoryDoubleSourceTreeExit.
Import ListNotations.
Set Implicit Arguments.

(** Decoder acceptance closes source reconstruction, each shared layout and all
    observed-header write exclusions. The accepted-entry facts and header words
    are the remaining dynamic obligations for guard/capture and the factory. *)
Theorem checked_double_source_tree_source_Loop p source tree header_values fe ge locals temps memory after final :
  checked_double_source_tree p source=Some tree -> preserving_globals (globalenv p) ge ->
  double_source_tree_scope tree locals ->
  double_source_tree_model_facts tree [] header_values (fun _ => 0%Z) ge (double_source_tree_layouts tree) ->
  double_source_tree_header_words ge locals (double_source_tree_active_headers header_values tree) header_values memory ->
  (exec_stmt fe ge locals temps memory source E0 after final Out_normal <->
   SL.loop_semantics (double_source_tree_model (double_source_tree_parameters tree) O tree)
     (map header_values (double_source_tree_parameters tree))
     (RuntimeState (global_double_locations ge (double_source_tree_layouts tree)) memory)
     (RuntimeState (global_double_locations ge (double_source_tree_layouts tree)) final) /\
   after=double_source_tree_exit header_values tree temps).
Proof.
  intros ACCEPT GLOBAL SCOPE FACTS HEADERS.
  destruct (@checked_double_source_tree_sound p source tree ACCEPT) as [SOURCE [CHECK [WRITES LAYOUT]]].
  rewrite SOURCE.
  apply (@double_source_tree_source_Loop p tree [] (fun _ => 0%Z) fe ge locals (double_source_tree_layouts tree)
    (double_source_tree_active_headers header_values tree) header_values temps memory after final).
  - exact GLOBAL.
  - exact CHECK.
  - intros instruction MEMBER; eapply checked_double_source_tree_layout_certificate; eassumption.
  - exact SCOPE.
  - intros instruction header POINT OBSERVED.
    assert (PARAMETER : In header (double_source_tree_parameters tree)).
    { apply double_source_tree_parameter_membership; eapply double_source_tree_active_headers_subset; exact OBSERVED. }
    eapply double_source_tree_header_writes_check_sound; eassumption.
  - apply incl_refl.
  - exact FACTS.
  - split; [intros key MEMBER; contradiction|exact HEADERS].
Qed.

Print Assumptions checked_double_source_tree_source_Loop.
