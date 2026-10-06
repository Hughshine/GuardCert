From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops GuardMemoryNaryCompute GuardMemoryNaryAffineAccess GuardMemoryMultiPointerCompute
  GuardMemoryMultiPointerCells GuardMemoryLinearPointerSyntax GuardMemoryFootprintRestriction
  GuardMemoryFiniteFootprint GuardMemoryAffinePointerPairs GuardMemoryAffineParameterLoops
  GuardMemoryAffineParameterFootprint GuardMemoryAffineParameterPointerFootprint.
From GuardInterface Require Import ClightAffineEnvelope ClightSourceObservation
  ClightReadonlyLoadedTreeSynthesis ClightPointerEnvelopePairs ClightReadonlyRewrite GuardedRewrite.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition compile_affine_parameter_pointer_envelopes registers bounds operations :=
  compile_pointer_envelope_pairs 2 registers bounds
    (memory_affine_access_pairs (memory_linear_pointer_accesses operations)).

(** C_derive: separate the actual access footprint using a covering box. Entry
    scalar values may be negative; only geometry parameters enter the envelope. *)
Theorem affine_parameter_pointer_envelopes_nonalias expression operations parameters scalars
  limits layout scalar_ids temps extent column_cap :
  Forall (memory_multi_pointer_compute_valid limits layout scalar_ids extent) operations ->
  (2+length parameters)%nat = length layout ->
  4*extent <= Ptrofs.modulus ->
  (forall i, 0 <= i < L.eval_expr (parameters++scalars) (L.Var 0) ->
    L.eval_expr (i::parameters++scalars) expression <= column_cap) ->
  Forall (pointer_envelope_pair_separated temps
    [L.eval_expr (parameters++scalars) (L.Var 0);column_cap] parameters)
    (memory_affine_access_pairs (memory_linear_pointer_accesses operations)) ->
  locations_nonalias (memory_restrict_locations
    (memory_footprint_allowed (memory_affine_parameter_pointer_footprint expression
      (length scalar_ids) operations (parameters++scalars))) (memory_multi_pointer_locations temps extent)).
Proof.
  intros VALID LENGTH EXTENT BOUND PAIRS; eapply pointer_envelope_pairs_nonalias; [exact EXTENT| |exact PAIRS].
  intros cell MEMBER.
  apply (proj1 (@memory_affine_parameter_pointer_geometry_member expression operations parameters scalars
    limits layout scalar_ids extent cell VALID LENGTH)) in MEMBER as [access [coordinates [ACCESS [POINT SAME]]]].
  exists access,coordinates; split; [exact ACCESS|split; [|exact SAME]].
  eapply memory_affine_parameter_points_box; [exact BOUND|exact POINT].
Qed.

(** C_guard and C_derive compose here. Word/range facts and observations are
    explicit entry obligations; the eventual source matcher must derive them.
    This theorem alone is not a source-derived guarded rewrite certificate. *)
Theorem compiled_affine_parameter_pointer_envelopes_sound expression operations parameters scalars
  limits layout scalar_ids extent column_cap registers bounds tree ge locals temps memory :
  Forall (memory_multi_pointer_compute_valid limits layout scalar_ids extent) operations ->
  (2+length parameters)%nat = length layout ->
  4*extent <= Ptrofs.modulus ->
  (forall i, 0 <= i < L.eval_expr (parameters++scalars) (L.Var 0) ->
    L.eval_expr (i::parameters++scalars) expression <= column_cap) ->
  compile_affine_parameter_pointer_envelopes registers bounds operations = Some tree ->
  affine_registers_view registers
    ([L.eval_expr (parameters++scalars) (L.Var 0);column_cap]++parameters) temps ->
  Forall2 (fun value limit => 0 <= value < limit)
    ([L.eval_expr (parameters++scalars) (L.Var 0);column_cap]++parameters) bounds ->
  (forall pair, In pair (memory_affine_access_pairs (memory_linear_pointer_accesses operations)) ->
    observed_pointer_domain [memory_nary_access_array (fst pair);memory_nary_access_array (snd pair)]
      (Entry ge locals temps memory)) ->
  (exists answer, decision_run (Entry ge locals temps memory) tree answer) /\
  (decision_run (Entry ge locals temps memory) tree true ->
    locations_nonalias (memory_restrict_locations
      (memory_footprint_allowed (memory_affine_parameter_pointer_footprint expression
        (length scalar_ids) operations (parameters++scalars))) (memory_multi_pointer_locations temps extent))).
Proof.
  intros VALID LENGTH EXTENT BOUND COMPILE VIEW RANGES OBSERVED.
  destruct (@compiled_pointer_envelope_pairs_sound 2 registers bounds
    (memory_affine_access_pairs (memory_linear_pointer_accesses operations)) tree ge locals temps memory
    [L.eval_expr (parameters++scalars) (L.Var 0);column_cap] parameters COMPILE eq_refl VIEW RANGES OBSERVED)
    as [SAFE SOUND].
  split; [exact SAFE|intro ACCEPT].
  eapply affine_parameter_pointer_envelopes_nonalias;
    [exact VALID|exact LENGTH|exact EXTENT|exact BOUND|apply SOUND; exact ACCEPT].
Qed.

(** The framework consumes this readonly certificate. D and its entry facts
    remain explicit obligations of the language/domain instance; D does not
    contain the non-alias presumption established on acceptance. *)
Theorem affine_parameter_pointer_envelope_condition fe O (observe : fragment_observation -> O -> Prop)
  (D : clight_entry -> Prop) expression operations limits layout scalar_ids extent registers bounds tree
  (parameters scalars : clight_entry -> list Z) (column_cap : clight_entry -> Z) :
  Forall (memory_multi_pointer_compute_valid limits layout scalar_ids extent) operations ->
  4*extent <= Ptrofs.modulus ->
  compile_affine_parameter_pointer_envelopes registers bounds operations = Some tree ->
  (forall entry, D entry -> (2+length (parameters entry))%nat = length layout) ->
  (forall entry, D entry -> forall i, 0 <= i < L.eval_expr (parameters entry++scalars entry) (L.Var 0) ->
    L.eval_expr (i::parameters entry++scalars entry) expression <= column_cap entry) ->
  (forall entry, D entry -> affine_registers_view registers
    ([L.eval_expr (parameters entry++scalars entry) (L.Var 0);column_cap entry]++parameters entry)
    (entry_temps entry)) ->
  (forall entry, D entry -> Forall2 (fun value limit => 0 <= value < limit)
    ([L.eval_expr (parameters entry++scalars entry) (L.Var 0);column_cap entry]++parameters entry) bounds) ->
  (forall entry, D entry -> forall pair,
    In pair (memory_affine_access_pairs (memory_linear_pointer_accesses operations)) ->
    observed_pointer_domain [memory_nary_access_array (fst pair);memory_nary_access_array (snd pair)] entry) ->
  readonly_condition (readonly_clight_host fe observe) D
    (fun entry => locations_nonalias (memory_restrict_locations
      (memory_footprint_allowed (memory_affine_parameter_pointer_footprint expression (length scalar_ids) operations
        (parameters entry++scalars entry))) (memory_multi_pointer_locations (entry_temps entry) extent))) tree.
Proof.
  intros VALID EXTENT COMPILE LENGTH COVERAGE VIEW RANGES OBSERVATIONS.
  assert (CORRECT : forall entry, D entry ->
    (exists answer, decision_run entry tree answer) /\
    (decision_run entry tree true -> locations_nonalias (memory_restrict_locations
      (memory_footprint_allowed (memory_affine_parameter_pointer_footprint expression (length scalar_ids) operations
        (parameters entry++scalars entry))) (memory_multi_pointer_locations (entry_temps entry) extent)))).
  { intros entry DOMAIN; destruct entry as [ge locals temps memory].
    eapply compiled_affine_parameter_pointer_envelopes_sound;
      [exact VALID|apply LENGTH; exact DOMAIN|exact EXTENT|apply COVERAGE; exact DOMAIN|exact COMPILE|
       apply VIEW; exact DOMAIN|apply RANGES; exact DOMAIN|apply OBSERVATIONS; exact DOMAIN]. }
  constructor.
  - intros entry DOMAIN; destruct (proj1 (CORRECT entry DOMAIN)) as [answer RUN].
    eapply readonly_decision_run_safe; exact RUN.
  - intros entry DOMAIN; destruct (proj1 (CORRECT entry DOMAIN)) as [answer RUN].
    exists answer,entry; split; [exact RUN|reflexivity].
  - intros entry answer checked DOMAIN [RUN SAME]; split; [exact SAME|intro ACCEPT; subst answer].
    apply (proj2 (CORRECT entry DOMAIN)); exact RUN.
Qed.

Print Assumptions affine_parameter_pointer_envelopes_nonalias.
Print Assumptions compiled_affine_parameter_pointer_envelopes_sound.
Print Assumptions affine_parameter_pointer_envelope_condition.
