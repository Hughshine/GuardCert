From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops GuardMemoryNaryCompute GuardMemoryNaryAffineAccess
  GuardMemoryMultiPointerCompute GuardMemoryMultiPointerCells GuardMemoryLinearPointerSyntax
  GuardMemoryAffinePointerPairs GuardMemoryFootprintRestriction GuardMemoryFiniteFootprint
  GuardMemoryAffineParameterFootprint GuardMemoryAffineParameterPointerFootprint.
From GuardInterface Require Import ClightAffineEnvelope ClightSourceObservation ClightReadonlyLoadedTreeSynthesis
  ClightAffineParameterPointerEnvelope.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition triangle_pointer_inner_bound := L.Sum (L.Var 0) (L.Constant 1).

Lemma triangle_pointer_actual_points N scalars i j :
  In [i;j] (memory_affine_parameter_points triangle_pointer_inner_bound (N::scalars)) <->
    0 <= i < N /\ 0 <= j <= i.
Proof.
  rewrite memory_affine_parameter_point_member; cbn [L.eval_expr triangle_pointer_inner_bound]; split.
  - intros [x [y [SAME [X Y]]]]; injection SAME; intros; subst.
    cbn [L.eval_expr triangle_pointer_inner_bound nth] in X,Y; lia.
  - intros [I J]; exists i,j; split; [reflexivity|].
    cbn [L.eval_expr triangle_pointer_inner_bound nth]; lia.
Qed.

(** This is a concrete domain instantiation of the condition certificate.
    The complete source selector and positive-header short circuit are separate
    installation obligations. There are no scalar sign assumptions here. *)
Theorem compiled_triangle_pointer_envelopes_sound operations scalars limits layout scalar_ids extent
  N registers bounds tree ge locals temps memory :
  Forall (memory_multi_pointer_compute_valid limits layout scalar_ids extent) operations ->
  length layout = 3%nat ->
  4*extent <= Ptrofs.modulus ->
  compile_affine_parameter_pointer_envelopes registers bounds operations = Some tree ->
  affine_registers_view registers [N;N;N] temps ->
  Forall2 (fun value limit => 0 <= value < limit) [N;N;N] bounds ->
  (forall pair, In pair (memory_affine_access_pairs (memory_linear_pointer_accesses operations)) ->
    observed_pointer_domain [memory_nary_access_array (fst pair);memory_nary_access_array (snd pair)]
      (Entry ge locals temps memory)) ->
  (exists answer, decision_run (Entry ge locals temps memory) tree answer) /\
  (decision_run (Entry ge locals temps memory) tree true ->
    locations_nonalias (memory_restrict_locations
      (memory_footprint_allowed (memory_affine_parameter_pointer_footprint triangle_pointer_inner_bound
        (length scalar_ids) operations (N::scalars))) (memory_multi_pointer_locations temps extent))).
Proof.
  intros VALID LENGTH EXTENT COMPILE VIEW RANGES OBSERVED.
  eapply (@compiled_affine_parameter_pointer_envelopes_sound triangle_pointer_inner_bound operations [N] scalars
    limits layout scalar_ids extent N registers bounds tree ge locals temps memory);
    [exact VALID|cbn; lia|exact EXTENT| |exact COMPILE|exact VIEW|exact RANGES|exact OBSERVED].
  intros i I; change (0 <= i < N) in I; change (i+1 <= N); lia.
Qed.

Print Assumptions triangle_pointer_actual_points.
Print Assumptions compiled_triangle_pointer_envelopes_sound.
