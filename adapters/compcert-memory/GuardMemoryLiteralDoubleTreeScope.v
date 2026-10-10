From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightGlobalScope ClightRegionProgress.
From GuardMemory Require Import GuardMemoryDynamicTensorLayout GuardMemoryDoubleAffineSourceAccess
  GuardMemoryDoubleSourceInstruction GuardMemoryDoubleSourceTreeData GuardMemoryDoubleSourceTreeState GuardMemoryDoubleTreeEntry
  GuardMemoryDoubleTensorBackend GuardMemoryLiteralDoubleTreeData GuardMemoryLiteralDoubleTreeDecode
  GuardMemoryLiteralDoubleTreeProgress GuardMemoryLiteralDoubleTreeFacts.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Fixed model parameter names are not globals. Only the array registry
    contributes to the host's C global-scope obligation. *)
Definition literal_double_tree_public_globals tree :=
  map fst (PTree.elements (double_source_tree_layouts (literal_double_tree_skeleton tree))).
Theorem literal_double_tree_layout_span_sound tree ge locals :
  double_tree_layout_span_check (literal_double_tree_skeleton tree)=true ->
  locals_avoid (literal_double_tree_public_globals tree) locals ->
  double_tensor_static ge locals (double_source_tree_layouts (literal_double_tree_skeleton tree)).
Proof.
  intros CHECK LOCAL identifier dimensions LAYOUT.
  pose proof (@PTree.elements_correct (list Z) _ identifier dimensions LAYOUT) as MEMBER; split.
  - apply LOCAL; unfold literal_double_tree_public_globals; apply in_map_iff.
    exists (identifier,dimensions); auto.
  - unfold double_tree_layout_span_check in CHECK.
    apply forallb_forall with (x:=(identifier,dimensions)) in CHECK;
      [cbn [snd] in CHECK; apply Z.leb_le; exact CHECK|exact MEMBER].
Qed.
Theorem checked_literal_double_tree_public_scope p source tree locals :
  checked_literal_double_source_tree p source=Some tree ->
  locals_avoid (literal_double_tree_public_globals tree) locals ->
  double_source_tree_scope (literal_double_tree_skeleton tree) locals.
Proof.
  intros CHECK LOCAL instruction POINT identifier MEMBER.
  unfold double_source_instruction_globals in MEMBER.
  apply in_map_iff in MEMBER as [access [SAME ACCESS]]; subst identifier.
  apply LOCAL; unfold literal_double_tree_public_globals; apply in_map_iff.
  exists (fst (double_affine_source_function access),double_affine_source_dimensions access).
  split; [reflexivity|apply PTree.elements_correct].
  apply (@checked_literal_double_tree_shared_layout p source tree CHECK instruction POINT access ACCESS).
Qed.
Definition literal_double_tree_source_globals p source := match checked_literal_double_source_tree p source with
  | Some tree=>literal_double_tree_public_globals tree | None=>[] end.
Definition literal_double_tree_progress_supported p source := match checked_literal_double_source_tree p source with
  | Some tree=>literal_double_source_tree_active_root tree | None=>false end.
Theorem literal_double_tree_progress_supported_sound p source :
  literal_double_tree_progress_supported p source=true -> exists MODEL : region_progress source, True.
Proof.
  unfold literal_double_tree_progress_supported.
  destruct (checked_literal_double_source_tree p source) as [tree|] eqn:CHECK; [|discriminate].
  intro ACTIVE; destruct (@checked_literal_double_source_tree_sound p source tree CHECK) as [SHAPE [TREE LAYOUT]].
  rewrite SHAPE; exists (@literal_double_source_tree_region_progress p [] tree TREE ACTIVE); exact I.
Qed.
Print Assumptions literal_double_tree_layout_span_sound.
Print Assumptions checked_literal_double_tree_public_scope.
Print Assumptions literal_double_tree_progress_supported_sound.
