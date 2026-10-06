From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightCountedLoop ClightTempFrame ClightRedundantSet.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryNaryCompute GuardMemoryNaryRanges
  GuardMemoryAffineInnerPointerSyntax GuardMemoryAffineInnerPointerSourceDomain GuardMemoryParametricGuard
  GuardMemoryAffinePointerLoadedDomain GuardMemoryWriteReceipts GuardMemoryAffineRowSeparation
  GuardMemoryAffineInnerPointerRegionSource.
From GuardInterface Require Import ClightAffineInnerPointerSourceGuard ClightAffinePreparedState
  ClightAffinePreparedRows ClightAffinePreparedFootprints ClightLoadedRowPrefix ClightStorePermissions ClightPreloadSnapshot.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition affine_loaded_package_prefix source (package : memory_affine_inner_pointer_package source) pointer fe :=
  @loaded_row_prefix fe (affine_inner_pointer_row (affine_inner_pointer_shape package))
    (affine_inner_pointer_bound (affine_inner_pointer_shape package)) pointer
    (affine_inner_pointer_outer_body (affine_inner_pointer_shape package)) (affine_prepared_stable package pointer)
    (affine_inner_pointer_ready package).

Section PREFIX.
Variable source : statement.
Variable package : memory_affine_inner_pointer_package source.
Variable pointer : ident.
Let shape := affine_inner_pointer_shape package.
Let row := affine_inner_pointer_row shape.
Let cache := affine_inner_pointer_bound shape.
Let column := affine_inner_pointer_column shape.
Let inner_bound := affine_inner_pointer_inner_bound shape.
Let CERT := affine_inner_pointer_syntax package.
Hypothesis FRESH : pointer <> row /\ pointer <> column /\ pointer <> inner_bound.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.

Lemma affine_loaded_prefix_parameter : In pointer (affine_prepared_stable package pointer).
Proof. left; reflexivity. Qed.
Lemma affine_loaded_prefix_fresh_row : ~ In row (affine_prepared_stable package pointer).
Proof.
  intro MEMBER; exact (proj1 (@affine_prepared_external_protected source package pointer FRESH row MEMBER) eq_refl).
Qed.

Theorem affine_loaded_package_prefix_initial entry :
  memory_affine_pointer_loaded_completed package pointer fe entry -> affine_inner_pointer_ready package entry ->
  affine_loaded_package_prefix package pointer fe 0 entry.
Proof.
  intros [DOMAIN [after [final SOURCE]]] READY.
  destruct DOMAIN as [ROW_DOMAIN [SNAPSHOT OBSERVED]].
  destruct SNAPSHOT as [word [block [offset [CACHE [POINTER READ]]]]].
  change ((entry_temps entry) ! cache = Some (Vint word)) in CACHE.
  assert (CAP : signed_range (affine_inner_pointer_row_limit package)).
  { pose proof (affine_inner_pointer_control_limits CERT) as CAPS; inversion CAPS; subst; tauto. }
  destruct (@memory_affine_inner_pointer_header_sound shape (affine_inner_pointer_row_limit package) entry CAP
    ROW_DOMAIN (affine_prepared_cache_domain READY) (affine_inner_pointer_ready_header READY)) as [ZERO RANGE].
  pose proof (affine_prepared_count_range READY) as COUNT.
  unfold affine_loaded_package_prefix,loaded_row_prefix; fold shape row cache.
  split; [exact READY|split; [exists word; exact CACHE|split;
    [change (0 <= 0 <= affine_prepared_count package entry); lia|]]].
  exists block,offset,(entry_temps entry),(entry_memory entry),after,final.
  assert (LOAD : Mem.loadv Mint32 (entry_memory entry) (Vptr block offset) =
    Some (Vint (temp_word cache (entry_temps entry)))) by (unfold temp_word; rewrite CACHE; exact READ).
  split; [exact POINTER|split; [exact LOAD|split; [exact ZERO|split; [apply temp_agree_refl|
    split; [exact LOAD|split; [apply memory_accesses_back_refl|exact SOURCE]]]]]].
Qed.

Theorem affine_loaded_package_row_domain i entry :
  affine_loaded_package_prefix package pointer fe i entry -> i < affine_prepared_count package entry ->
  memory_affine_row_domain row column i (affine_inner_pointer_expression package) pointer
    (affine_inner_pointer_operations package) (Z.to_nat (affine_inner_pointer_column_limit package))
    affine_prepared_valuation (fun entry j => affine_prepared_point_values package entry i j)
    (fun entry => affine_prepared_upper package entry i) entry.
Proof.
  intros INV ACTIVE.
  assert (READY : affine_inner_pointer_ready package entry) by (exact (proj1 INV)).
  assert (I : 0 <= i < affine_prepared_count package entry) by
    (pose proof (proj1 (proj2 (proj2 INV))) as RANGE;
      change (0 <= i <= affine_prepared_count package entry) in RANGE; lia).
  assert (CAP : 0 < affine_inner_pointer_column_limit package /\ signed_range (affine_inner_pointer_column_limit package)).
  { pose proof (affine_inner_pointer_control_limits CERT) as CAPS; inversion CAPS; subst;
    match goal with REST : Forall _ [_] |- _ => inversion REST; subst; tauto end. }
  pose proof (@loaded_row_prefix_receipt fe row cache pointer (affine_inner_pointer_outer_body shape)
    (affine_prepared_stable package pointer) (affine_inner_pointer_ready package)
    (affine_prepared_upper package) (affine_prepared_point package)
    affine_loaded_prefix_parameter (@affine_prepared_outer_normal source package)
    (@affine_prepared_outer_quiet source package)
    (@affine_prepared_actual_row_decode source package pointer FRESH fe) i entry INV ACTIVE) as RECEIPT.
  destruct RECEIPT as [current [before [after [final [ROW [FRAME [BACK [BODY ITER]]]]]]]].
  unfold memory_affine_row_domain; split; [|split; [|split; [|split]]].
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
  - destruct INV as [_ [_ [_ [block [offset [temps [memory [last [finish [POINTER [READ REST]]]]]]]]]]].
    exists block,offset,(Vint (temp_word cache (entry_temps entry))); split; assumption.
Qed.
End PREFIX.

Print Assumptions affine_loaded_package_prefix_initial.
Print Assumptions affine_loaded_package_row_domain.
