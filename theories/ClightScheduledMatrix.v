From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import AbstractGuard CompCertMemoryEquivalence AbstractSchedule
  CompCertStoreSchedule CompCertIndexSchedule ClightGuard ClightCondition ClightRegionRule ClightRegionRewrite
  ClightFrontendLoopProtocol ClightFrontendRegion ClightMatrixStore ClightMatrixLoops
  ClightMatrixGuard ClightMatrixRegion ClightMatrixSelector.
From Guard Require Import ClightIndexedStores.
Import ListNotations.
Set Implicit Arguments.

(** The proposal contains only an instruction order. Its acceptance does not
    require trusting a scheduler or binding an external proof-producing tool. *)
Definition scheduled_matrix_rule {source d} (CERT : matrix_certificate source d)
  (order : list nat) (CHECK : check_index_schedule row_index_order order = true) :
  encoded_region_rule source
    (matrix_scheduled_target (described_array d) (matrix_row d) (matrix_column d) order).
Proof.
  refine {| region_rule_atoms := unit;
    region_rule_domain := matrix_guard_domain (matrix_row d) (matrix_bound d) (matrix_inner_bound d);
    region_rule_dimension := matrix_guard_dimension (matrix_row d) (matrix_bound d) (matrix_inner_bound d);
    region_rule_primitives := matrix_guard_primitives (matrix_row d) (matrix_bound d) (matrix_inner_bound d);
    region_rule_formula := Fact tt |}.
  - intros temps p locals le memory le' final RUN.
    rewrite (matrix_source_bound CERT) in RUN; unfold matrix_described_source in RUN.
    eapply matrix_source_guard_domain; [exact (matrix_distinct_row_column CERT)|
      exact (matrix_distinct_bound_column CERT)|exact (matrix_distinct_column_inner_bound CERT)|
      exact (matrix_body_bound CERT)|exact (matrix_outer_bound CERT)|exact RUN].
  - intros temps p locals le memory le' final RUN [ZERO [TWO INNER_TWO]].
    rewrite (matrix_source_bound CERT) in RUN; unfold matrix_described_source in RUN.
    change (le ! (matrix_row d) = Some (Vint (Int.repr 0))) in ZERO.
    change (le ! (matrix_bound d) = Some (Vint (Int.repr 2))) in TWO.
    change (le ! (matrix_inner_bound d) = Some (Vint (Int.repr 2))) in INNER_TWO.
    destruct (@matrix_source_decode (adapter_entry temps) (globalenv p) locals le memory
      (described_array d) (matrix_row d) (matrix_bound d) (matrix_column d) (matrix_inner_bound d)
      (matrix_inner_body d) (matrix_outer_body d) le' final
      (matrix_distinct_row_bound CERT) (matrix_distinct_row_column CERT) (matrix_distinct_bound_column CERT)
      (matrix_distinct_row_inner_bound CERT) (matrix_distinct_column_inner_bound CERT)
      (matrix_body_bound CERT) (matrix_outer_bound CERT) ZERO TWO INNER_TWO RUN)
      as [block [ARRAY [SCHEDULE EXIT]]].
    assert (TARGET : schedule_run compcert_store_scheduling
      (map (indexed_store_action block matrix_index_values) order) memory final).
    { eapply checked_index_schedule_preserves_actual_memory; [exact CHECK|exact SCHEDULE]. }
    exists final; split; [rewrite EXIT; eapply matrix_scheduled_target_encode; eauto|
      apply memory_equivalent_refl].
Defined.

Definition select_scheduled_matrix order source : option statement :=
  match propose_matrix_description source with
  | Some d => match check_matrix_description source d with
    | Some CERT => match Bool.bool_dec (check_index_schedule row_index_order order) true with
      | left CHECK => Some (generated_region (scheduled_matrix_rule CERT order CHECK))
      | right _ => None end
    | None => None end
  | None => None end.

Theorem select_scheduled_matrix_sound order source target :
  select_scheduled_matrix order source = Some target -> region_contract source target.
Proof.
  unfold select_scheduled_matrix; destruct (propose_matrix_description source) as [d|]; try discriminate.
  destruct (check_matrix_description source d) as [CERT|]; try discriminate.
  destruct (Bool.bool_dec (check_index_schedule row_index_order order) true) as [CHECK|]; try discriminate.
  intro SELECT; inversion SELECT; subst; apply encoded_region_rule_sound.
Qed.

Example reversed_matrix_schedule_selected : exists target,
  select_scheduled_matrix [3%nat;2%nat;1%nat;0%nat] example_matrix_source = Some target.
Proof. eexists; vm_compute; reflexivity. Qed.
Example duplicate_matrix_schedule_refused :
  select_scheduled_matrix [0%nat;2%nat;1%nat;1%nat] example_matrix_source = None.
Proof. vm_compute; reflexivity. Qed.
Example missing_matrix_schedule_refused :
  select_scheduled_matrix [0%nat;2%nat;1%nat] example_matrix_source = None.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions select_scheduled_matrix_sound.
