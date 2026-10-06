From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightCountedLoop ClightTempFrame
  ClightRedundantSet ClightLoopSyntax ClightRegionProgress ClightRectangularLoops CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax GuardMemoryAffineInnerPointerSourceDomain
  GuardMemoryAffineInnerPointerRegionSource GuardMemoryParametricGuard GuardMemoryParametricSourceClight
  GuardMemoryAffineDependentRow GuardMemoryWriteReceipts GuardMemoryAffineWriteSeparation.
From GuardInterface Require Import ClightDependentBoundSyntax ClightDependentHeaderObservations
  ClightObservedHeaderPrefix ClightAffineInnerPointerSourceGuard ClightAffinePreparedState
  ClightAffinePreparedRows ClightAffinePreparedFootprints ClightSourceObservation ClightStorePermissions.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition affine_dependent_loaded_source source (package : memory_affine_inner_pointer_package source) root :=
  dependent_bound_loop (affine_inner_pointer_row (affine_inner_pointer_shape package)) root
    (affine_inner_pointer_outer_body (affine_inner_pointer_shape package)).
Definition affine_dependent_loaded_completed source (package : memory_affine_inner_pointer_package source)
  root pointer_cache fe entry :=
  register_domain (affine_inner_pointer_row (affine_inner_pointer_shape package)) entry /\
  dependent_cached_header root pointer_cache (affine_inner_pointer_bound (affine_inner_pointer_shape package)) entry /\
  observed_pointer_domain (affine_inner_pointer_pointers package) entry /\ exists after final,
    exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
      (affine_dependent_loaded_source package root) E0 after final Out_normal.
Definition affine_dependent_ready source (package : memory_affine_inner_pointer_package source) root pointer_cache entry :=
  affine_inner_pointer_ready package entry /\
  dependent_cached_header root pointer_cache (affine_inner_pointer_bound (affine_inner_pointer_shape package)) entry.
Definition affine_dependent_stable source (package : memory_affine_inner_pointer_package source) root pointer_cache :=
  root::affine_prepared_stable package pointer_cache.
Definition affine_dependent_package_prefix source (package : memory_affine_inner_pointer_package source) root pointer_cache fe :=
  @observed_header_prefix fe (affine_inner_pointer_row (affine_inner_pointer_shape package))
    (affine_inner_pointer_bound (affine_inner_pointer_shape package))
    (dependent_bound_test (affine_inner_pointer_row (affine_inner_pointer_shape package)) root)
    (affine_inner_pointer_outer_body (affine_inner_pointer_shape package))
    (affine_dependent_stable package root pointer_cache) (affine_dependent_ready package root pointer_cache)
    (dependent_header_observations root pointer_cache (affine_inner_pointer_bound (affine_inner_pointer_shape package))).

Section PREFIX.
Variable source : statement.
Variable package : memory_affine_inner_pointer_package source.
Variables root pointer_cache : ident.
Let shape := affine_inner_pointer_shape package.
Let row := affine_inner_pointer_row shape.
Let column := affine_inner_pointer_column shape.
Let inner_bound := affine_inner_pointer_inner_bound shape.
Let cache := affine_inner_pointer_bound shape.
Let CERT := affine_inner_pointer_syntax package.
Hypothesis ROOT_FRESH : root <> row /\ root <> column /\ root <> inner_bound.
Hypothesis POINTER_FRESH : pointer_cache <> row /\ pointer_cache <> column /\ pointer_cache <> inner_bound.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.

Lemma affine_dependent_protected identifier :
  In identifier (affine_dependent_stable package root pointer_cache) ->
  identifier <> row /\ identifier <> column /\ identifier <> inner_bound.
Proof.
  intros [<-|MEMBER]; [exact ROOT_FRESH|].
  exact (@affine_prepared_external_protected source package pointer_cache POINTER_FRESH identifier MEMBER).
Qed.
Lemma affine_dependent_fresh_row : ~ In row (affine_dependent_stable package root pointer_cache).
Proof. intro MEMBER; exact (proj1 (affine_dependent_protected MEMBER) eq_refl). Qed.

Lemma affine_dependent_actual_header entry i current memory :
  affine_dependent_ready package root pointer_cache entry ->
  0 <= i <= affine_prepared_count package entry -> current ! row = Some (Vint (Int.repr i)) ->
  temp_agree (affine_dependent_stable package root pointer_cache) (entry_temps entry) current ->
  header_observations_match (dependent_header_observations root pointer_cache cache entry) memory ->
  expression_test (dependent_bound_test row root) (Entry (entry_ge entry) (entry_env entry) current memory)
    (i <? affine_prepared_count package entry).
Proof.
  intros [READY CACHED] RANGE ROW FRAME READS.
  eapply (@dependent_header_from_observations row root pointer_cache cache
    (affine_dependent_stable package root pointer_cache) entry i current memory);
    [left; reflexivity|exact CACHED|exact RANGE|exact ROW|exact FRAME|exact READS].
Qed.

(** The extra root is protected by the checked body's exact exit; its memory
    cell is allowed to change. The old actual decoder supplies every point. *)
Theorem affine_dependent_actual_row_decode entry i current memory after final :
  affine_dependent_ready package root pointer_cache entry ->
  0 <= i < affine_prepared_count package entry -> current ! row = Some (Vint (Int.repr i)) ->
  temp_agree (affine_dependent_stable package root pointer_cache) (entry_temps entry) current ->
  exec_stmt fe (entry_ge entry) (entry_env entry) current memory (affine_inner_pointer_outer_body shape)
    E0 after final Out_normal ->
  counted_iterations (affine_prepared_point package entry i) (Z.to_nat (affine_prepared_upper package entry i))
    0 memory final /\ after ! row = current ! row /\
    temp_agree (affine_dependent_stable package root pointer_cache) current after.
Proof.
  intros [READY CACHED] RANGE ROW FRAME BODY.
  assert (OLD_FRAME : temp_agree (affine_prepared_stable package pointer_cache) (entry_temps entry) current).
  { eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER; right; exact MEMBER. }
  destruct (@affine_prepared_actual_row_decode_exact source package pointer_cache POINTER_FRESH fe
    entry i current memory after final READY RANGE ROW OLD_FRAME BODY) as [ITER EXIT].
  fold shape column inner_bound in EXIT.
  split; [exact ITER|rewrite EXIT; split].
  - pose proof (affine_inner_pointer_rc CERT) as RC; change (row <> column) in RC.
    pose proof (affine_inner_pointer_rk CERT) as RK; change (row <> inner_bound) in RK.
    unfold memory_parametric_settle; rewrite !PTree.gso by congruence; reflexivity.
  - unfold memory_parametric_settle; eapply temp_agree_trans; apply temp_agree_set.
    + intro MEMBER; exact (proj2 (proj2 (affine_dependent_protected MEMBER)) eq_refl).
    + intro MEMBER; exact (proj1 (proj2 (affine_dependent_protected MEMBER)) eq_refl).
Qed.

Theorem affine_dependent_prefix_initial entry :
  affine_dependent_loaded_completed package root pointer_cache fe entry -> affine_inner_pointer_ready package entry ->
  affine_dependent_package_prefix package root pointer_cache fe 0 entry.
Proof.
  intros [ROW_DOMAIN [CACHED [OBSERVED [after [final SOURCE]]]]] READY.
  assert (CAP : signed_range (affine_inner_pointer_row_limit package)).
  { pose proof (affine_inner_pointer_control_limits CERT) as CAPS; inversion CAPS; subst; tauto. }
  destruct (@memory_affine_inner_pointer_header_sound shape (affine_inner_pointer_row_limit package) entry CAP
    ROW_DOMAIN (affine_prepared_cache_domain READY) (affine_inner_pointer_ready_header READY)) as [ZERO RANGE].
  apply (@observed_header_prefix_initial fe row cache (dependent_bound_test row root)
    (affine_inner_pointer_outer_body shape) (affine_dependent_stable package root pointer_cache)
    (affine_dependent_ready package root pointer_cache) (dependent_header_observations root pointer_cache cache)
    entry after final).
  - split; assumption.
  - exact (affine_prepared_cache_domain READY).
  - pose proof (affine_prepared_count_range READY); change (0 <= affine_prepared_count package entry); lia.
  - exact ZERO.
  - apply dependent_header_initial_observations; exact CACHED.
  - exact SOURCE.
Qed.

Theorem affine_dependent_package_row_domain i entry :
  affine_dependent_package_prefix package root pointer_cache fe i entry -> i < affine_prepared_count package entry ->
  memory_affine_dependent_row_domain row column i (affine_inner_pointer_expression package)
    root pointer_cache cache (affine_inner_pointer_operations package) (Z.to_nat (affine_inner_pointer_column_limit package))
    affine_prepared_valuation (fun entry j => affine_prepared_point_values package entry i j)
    (fun entry => affine_prepared_upper package entry i) entry.
Proof.
  intros INV ACTIVE.
  assert (READY : affine_inner_pointer_ready package entry) by (exact (proj1 (proj1 INV))).
  assert (CACHED : dependent_cached_header root pointer_cache cache entry) by (exact (proj2 (proj1 INV))).
  assert (I : 0 <= i < affine_prepared_count package entry).
  { pose proof (proj1 (proj2 (proj2 INV))) as RANGE; change (0 <= i <= affine_prepared_count package entry) in RANGE; lia. }
  assert (CAP : 0 < affine_inner_pointer_column_limit package /\ signed_range (affine_inner_pointer_column_limit package)).
  { pose proof (affine_inner_pointer_control_limits CERT) as CAPS; inversion CAPS; subst;
    match goal with REST : Forall _ [_] |- _ => inversion REST; subst; tauto end. }
  pose proof (@observed_header_prefix_receipt fe row cache (dependent_bound_test row root)
    (affine_inner_pointer_outer_body shape) (affine_dependent_stable package root pointer_cache)
    (affine_dependent_ready package root pointer_cache) (dependent_header_observations root pointer_cache cache)
    (affine_prepared_upper package) (affine_prepared_point package)
    (@affine_prepared_outer_normal source package) (@affine_prepared_outer_quiet source package)
    affine_dependent_actual_header affine_dependent_actual_row_decode i entry INV ACTIVE) as RECEIPT.
  destruct RECEIPT as [current [before [after [final [ROW [FRAME [BACK [BODY ITER]]]]]]]].
  unfold memory_affine_dependent_row_domain; split; [|split; [|split; [|split]]].
  - rewrite Z2Nat.id by lia; exact (proj1 (affine_prepared_upper_range READY I)).
  - apply affine_prepared_upper_at_math.
  - intros identifier READ OTHER COLUMN; apply (@affine_prepared_words source package entry READY identifier).
    apply affine_prepared_header_read; assumption.
  - intros j J; apply affine_prepared_write_probes_ready; [exact READY|exact I|exact J|].
    pose proof (@counted_pointer_sequence_write_receipts (entry_temps entry)
      (fun j => affine_prepared_point_values package entry i j) (affine_inner_pointer_operations package)
      (Z.to_nat (affine_prepared_upper package entry i)) 0 before final ITER j
      ltac:(rewrite Z2Nat.id by (pose proof (affine_prepared_upper_range READY I); lia); lia)) as WRITES.
    eapply Forall_impl; [|exact WRITES]; intros operation WRITE;
      eapply memory_write_receipt_back; [exact BACK|exact WRITE].
  - exact CACHED.
Qed.
End PREFIX.

Print Assumptions affine_dependent_protected.
Print Assumptions affine_dependent_fresh_row.
Print Assumptions affine_dependent_actual_header.
Print Assumptions affine_dependent_actual_row_decode.
Print Assumptions affine_dependent_prefix_initial.
Print Assumptions affine_dependent_package_row_domain.
