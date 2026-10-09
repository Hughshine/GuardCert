From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightGlobalScope.
From GuardMemory Require Import GuardMemoryDynamicTensorLayout GuardMemoryDoubleLocations
  GuardMemoryDoubleTensorBackend GuardMemoryDoubleAffineSourceAccess GuardMemoryDoubleSourceInstruction GuardMemoryDoubleInitializedReductionData
  GuardMemoryDoubleInitializedNestData GuardMemoryDoubleInitializedRawNest.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Relevant global names and target layout facts come from actual checked data.
    No equality with a benchmark's complete symbol map is required. *)
Definition double_initialized_public_globals description :=
  initialized_reduction_header description::
    map fst (PTree.elements (double_initialized_reduction_layouts description)).
Definition double_initialized_layout_span_check description := forallb
  (fun entry => 8*tensor_volume (snd entry)<=?Ptrofs.modulus)
  (PTree.elements (double_initialized_reduction_layouts description)).
Theorem double_initialized_layout_span_check_sound description ge locals :
  double_initialized_layout_span_check description=true ->
  locals_avoid (double_initialized_public_globals description) locals ->
  double_tensor_static ge locals (double_initialized_reduction_layouts description).
Proof.
  intros CHECK LOCAL identifier dimensions LAYOUT.
  pose proof (@PTree.elements_correct (list Z) (double_initialized_reduction_layouts description)
    identifier dimensions LAYOUT) as MEMBER.
  split.
  - apply LOCAL; unfold double_initialized_public_globals; right.
    apply in_map_iff; exists (identifier,dimensions); split; [reflexivity|exact MEMBER].
  - unfold double_initialized_layout_span_check in CHECK.
    apply forallb_forall with (x:=(identifier,dimensions)) in CHECK; [|exact MEMBER].
    cbn [snd] in CHECK; apply Z.leb_le; exact CHECK.
Qed.
Theorem checked_double_initialized_public_scope p source outers description locals :
  checked_double_initialized_raw_nest p [] source=Some (outers,description) ->
  locals_avoid (double_initialized_public_globals description) locals ->
  locals_avoid (double_initialized_reduction_globals description) locals.
Proof.
  intros CHECK LOCAL.
  destruct (@checked_double_initialized_raw_nest_sound p [] source outers description CHECK)
    as [RAW [CANONICAL EQUIV]].
  destruct (@checked_double_initialized_nest_sound p [] (double_initialized_nest_code outers description)
    outers description CANONICAL) as [CODE [LEAF FRESH]].
  destruct (@checked_double_initialized_reduction_sound p ([]++outers)
    (double_initialized_reduction_code description) description LEAF) as [_ [_ [_ STATIC]]].
  unfold double_initialized_reduction_static_check in STATIC.
  apply andb_true_iff in STATIC as [_ STATIC]; apply andb_true_iff in STATIC as [_ STATIC].
  apply andb_true_iff in STATIC as [_ STATIC]; apply andb_true_iff in STATIC as [_ REGISTRY].
  pose proof (@double_source_layout_check_sound (double_initialized_reduction_layouts description)
    (double_initialized_reduction_accesses description) REGISTRY) as LAYOUT.
  intros identifier MEMBER; unfold double_initialized_reduction_globals in MEMBER.
  destruct MEMBER as [SAME|MEMBER].
  - subst identifier; apply LOCAL; unfold double_initialized_public_globals; left; reflexivity.
  - apply in_map_iff in MEMBER as [access [SAME ACCESS]]; subst identifier.
    apply LOCAL; unfold double_initialized_public_globals; right.
    apply in_map_iff; exists (fst (double_affine_source_function access),double_affine_source_dimensions access).
    split; [reflexivity|apply PTree.elements_correct; apply LAYOUT; exact ACCESS].
Qed.

Print Assumptions double_initialized_layout_span_check_sound.
Print Assumptions checked_double_initialized_public_scope.
