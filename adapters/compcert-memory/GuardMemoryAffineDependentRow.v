From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightCountedLoop CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryNaryCompute GuardMemoryAffineSourceExpressions
  GuardMemoryAffineAddressSpecialization GuardMemoryAffineWriteSeparation GuardMemoryAffineChunkWriteSeparation
  GuardMemoryObservationStability GuardMemoryMultiPointerSequence GuardMemoryAffineRowSeparation.
From GuardInterface Require Import GuardInterface GuardedRewrite ClightReadonlyRewrite
  ClightReadonlyExpressionScan ClightDependentHeaderObservations.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_affine_dependent_row_probe row column i expression root pointer_cache operations cap :=
  readonly_bound_expression_scan (memory_affine_row_bound row column i expression)
    (fun j => memory_affine_dependent_write_probe row column i j root pointer_cache operations) cap 0.

(** This domain concerns one reached source row only. The actual row decoder
    supplies its write receipts, and existing arithmetic/range certificates
    supply the other fields. Future rows and bound stability are absent. *)
Definition memory_affine_dependent_row_domain row column i expression root pointer_cache cache operations cap
  (valuation : clight_entry -> ident -> Z) (values : clight_entry -> Z -> list Z)
  (width : clight_entry -> Z) entry :=
  0 <= width entry <= Z.of_nat cap /\
  memory_source_affine_math (memory_affine_at_value row column i 0 (valuation entry)) expression = width entry /\
  (forall identifier, In identifier (memory_source_affine_reads expression) ->
    identifier <> row -> identifier <> column ->
    (entry_temps entry) ! identifier = Some (Vint (Int.repr (valuation entry identifier)))) /\
  (forall j, 0 <= j < width entry ->
    Forall (memory_affine_write_ready row column i j (valuation entry) (values entry j) entry) operations) /\
  dependent_cached_header root pointer_cache cache entry.

Section ROW.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable O : Type.
Variable observe : fragment_observation -> O -> Prop.
Variables row column root pointer_cache cache : ident.
Variable i : Z.
Variable expression : memory_source_affine.
Variable operations : list memory_nary_compute.
Variable cap : nat.
Variables valuation : clight_entry -> ident -> Z.
Variable values : clight_entry -> Z -> list Z.
Variable width : clight_entry -> Z.
Hypothesis CAP : Z.of_nat cap <= Int.max_signed.
Let domain := memory_affine_dependent_row_domain row column i expression root pointer_cache cache operations cap valuation values width.
Let property := fun j entry => memory_affine_dependent_write_separated (values entry j) root pointer_cache cache operations entry.

Lemma memory_affine_dependent_row_bound_value entry : domain entry ->
  eval_expr (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
    (memory_affine_row_bound row column i expression) (Vint (Int.repr (width entry))).
Proof.
  intros [RANGE [MATH [WORDS REST]]]; rewrite <- MATH; apply memory_affine_at_evaluation; exact WORDS.
Qed.

Definition memory_affine_dependent_row_point_condition j : readonly_condition (readonly_clight_host fe observe)
  (fun entry => domain entry /\ 0 <= j < width entry) (property j)
  (memory_affine_dependent_write_probe row column i j root pointer_cache operations).
Proof.
  assert (DOMAIN : forall entry, domain entry -> 0 <= j < width entry ->
    memory_affine_dependent_write_domain row column i j (valuation entry) (values entry j) root pointer_cache cache operations entry).
  { intros entry [RANGE [MATH [WORDS [READY LOAD]]]] J; split; [apply READY; exact J|exact LOAD]. }
  constructor.
  - intros entry [D J]; apply (readonly_safe (@memory_affine_dependent_write_condition fe O observe
      row column i j (valuation entry) (values entry j) root pointer_cache cache operations)); apply DOMAIN; assumption.
  - intros entry [D J]; apply (readonly_available (@memory_affine_dependent_write_condition fe O observe
      row column i j (valuation entry) (values entry j) root pointer_cache cache operations)); apply DOMAIN; assumption.
  - intros entry answer checked [D J] RUN; apply (readonly_sound (@memory_affine_dependent_write_condition fe O observe
      row column i j (valuation entry) (values entry j) root pointer_cache cache operations)); [apply DOMAIN; assumption|exact RUN].
Defined.

Definition memory_affine_dependent_row_condition : readonly_condition (readonly_clight_host fe observe)
  domain (fun entry => forall j, 0 <= j < width entry -> property j entry)
  (memory_affine_dependent_row_probe row column i expression root pointer_cache operations cap).
Proof.
  eapply readonly_condition_restrict.
  - exact (@readonly_expression_scan_condition fe O observe (memory_affine_row_bound row column i expression)
      width domain (fun j => memory_affine_dependent_write_probe row column i j root pointer_cache operations) property
      (memory_source_affine_type _) memory_affine_dependent_row_bound_value
      ltac:(intros entry [RANGE REST]; lia) memory_affine_dependent_row_point_condition cap).
  - intros entry D; split; [exact D|destruct D as [RANGE REST]; lia].
Defined.

Theorem memory_affine_dependent_row_preserves entry :
  domain entry -> decision_run entry (memory_affine_dependent_row_probe row column i expression
    root pointer_cache operations cap) true ->
  forall j before after, 0 <= j < width entry ->
    memory_multi_pointer_sequence_physical (entry_temps entry) (values entry j) operations before after ->
  forall observation, In observation (dependent_header_observations root pointer_cache cache entry) ->
    location_load (fst observation) after = location_load (fst observation) before.
Proof.
  intros DOMAIN RUN j before after J STEP observation MEMBER.
  destruct (readonly_sound memory_affine_dependent_row_condition entry true entry DOMAIN
    (conj RUN eq_refl)) as [SAME SOUND].
  eapply memory_pointer_sequence_observation_preserved; [apply (SOUND eq_refl j J observation MEMBER)|exact STEP].
Qed.
End ROW.

Print Assumptions memory_affine_dependent_row_bound_value.
Print Assumptions memory_affine_dependent_row_point_condition.
Print Assumptions memory_affine_dependent_row_condition.
Print Assumptions memory_affine_dependent_row_preserves.
