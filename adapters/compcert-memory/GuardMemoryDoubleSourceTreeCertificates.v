From Stdlib Require Import List.
From compcert.lib Require Import Maps.
From compcert.common Require Import Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightGlobalScope ClightRegionProgress.
From GuardMemory Require Import GuardMemoryDoubleSourceInstruction GuardMemoryDoubleSourceTransport
  GuardMemoryDoubleSourceTreeData GuardMemoryDoubleSourceTreeDecode
  GuardMemoryDoubleSourceTreeEffects GuardMemoryDoubleSourceTreeProgress.
Import ListNotations.
Set Implicit Arguments.

(** Static acceptance produces these certificates. Language/domain clients do
    not supply a semantic callback for each selected source assignment. *)
Definition checked_double_source_tree_progress p source tree
  (CHECK : checked_double_source_tree p source=Some tree)
  (ACTIVE : double_source_tree_active_root tree=true) : region_progress source.
Proof.
  destruct (@checked_double_source_tree_sound p source tree CHECK) as [SOURCE [TREE _]].
  rewrite SOURCE; apply double_source_tree_region_progress with (p:=p) (controls:=[]); assumption.
Defined.

Theorem checked_double_source_tree_header_certificate p source tree fe ge locals temps memory trace after final outcome
  header header_block :
  checked_double_source_tree p source=Some tree ->
  In header (double_source_tree_parameters tree) -> preserving_globals (globalenv p) ge ->
  locals_avoid (double_tree_write_globals tree) locals -> Genv.find_symbol ge header=Some header_block ->
  exec_stmt fe ge locals temps memory source trace after final outcome ->
  (forall chunk offset, Mem.load chunk final header_block offset=Mem.load chunk memory header_block offset) /\
  (forall block offset kind permission,
    Mem.perm final block offset kind permission <-> Mem.perm memory block offset kind permission).
Proof.
  intros CHECK MEMBER GLOBAL LOCAL HEADER RUN.
  destruct (@checked_double_source_tree_sound p source tree CHECK) as [SOURCE [TREE [WRITES LAYOUT]]].
  rewrite SOURCE in RUN; eapply checked_double_source_tree_raw_header_frame; eassumption.
Qed.

Theorem checked_double_source_tree_layout_certificate p source tree instruction :
  checked_double_source_tree p source=Some tree -> In instruction (double_source_tree_instructions tree) ->
  double_source_layout_certificate instruction (double_source_tree_layouts tree).
Proof.
  intros CHECK POINT access MEMBER.
  destruct (@checked_double_source_tree_sound p source tree CHECK) as [SOURCE [TREE [WRITES LAYOUT]]].
  unfold double_source_tree_layout_check in LAYOUT.
  apply (@double_source_layout_check_sound (double_source_tree_layouts tree) (double_source_tree_accesses tree) LAYOUT access).
  unfold double_source_tree_accesses; apply in_flat_map; exists instruction; auto.
Qed.

Print Assumptions checked_double_source_tree_progress.
Print Assumptions checked_double_source_tree_header_certificate.
Print Assumptions checked_double_source_tree_layout_certificate.
