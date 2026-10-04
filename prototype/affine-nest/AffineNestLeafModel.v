From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Coqlib Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightSyntaxEquality ClightFiniteRegion ClightStraightLine
  ClightTempFrame ClightLoopSyntax ClightRegionProgress.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops
  GuardMemoryNaryCompute GuardMemoryNaryLoops GuardMemoryPointerCompute GuardMemoryPointerSequence GuardMemoryMultiPointerCompute
  GuardMemoryMultiPointerSequence GuardMemoryMultiPointerIdentifiers GuardMemoryMultiPointerCells
  GuardMemoryIntervalBox GuardMemoryWindowCompute GuardMemoryWindowCells GuardMemoryWindowSequence
  GuardMemoryWindowCheck GuardMemoryMultiPointerComputeSyntax GuardMemoryPointerSourceWords
  GuardMemoryRecursiveSyntax.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** This certificate checks the real leaf independently of any rectangular
    source-loop skeleton. Its coordinate box can later be restricted by the
    affine domain. Bound helpers outside the explicit layout are refused. *)
Record affine_leaf_certificate source bounds lower upper layout scalars pointers operations := AffineLeafCertificate {
  affine_leaf_exact : flatten_region source=map memory_pointer_compute_statement operations;
  affine_leaf_valid : Forall (window_compute_valid bounds lower upper layout scalars) operations;
  affine_leaf_covered : Forall (memory_multi_pointer_operation_covered pointers) operations;
  affine_leaf_unique : NoDup(layout++scalars)
}.

Definition check_affine_leaf source bounds lower upper layout scalars pointers operations :
  option(affine_leaf_certificate source bounds lower upper layout scalars pointers operations).
Proof.
  destruct (list_eq_dec statement_eq (flatten_region source) (map memory_pointer_compute_statement operations)) as [EXACT|]; [|exact None].
  destruct (forallb (window_compute_check bounds lower upper layout scalars) operations) eqn:VALID; [|exact None].
  destruct (forallb (memory_multi_pointer_operation_covered_check pointers) operations) eqn:COVERED; [|exact None].
  destruct (memory_identifiers_unique_check (layout++scalars)) eqn:UNIQUE; [|exact None].
  assert (OPERATIONS:Forall (window_compute_valid bounds lower upper layout scalars) operations).
  { apply Forall_forall; intros operation MEMBER; apply window_compute_check_sound.
    apply forallb_forall with (x:=operation) in VALID; assumption. }
  assert (POINTERS:Forall (memory_multi_pointer_operation_covered pointers) operations).
  { apply Forall_forall; intros operation MEMBER; apply memory_multi_pointer_operation_covered_check_sound.
    apply forallb_forall with (x:=operation) in COVERED; assumption. }
  exact(Some(@AffineLeafCertificate source bounds lower upper layout scalars pointers operations
    EXACT OPERATIONS POINTERS (@memory_identifiers_unique_check_sound _ UNIQUE))).
Defined.

Lemma affine_leaf_normal source bounds lower upper layout scalars pointers operations
  (certificate:affine_leaf_certificate source bounds lower upper layout scalars pointers operations) :
  normal_statement source=true.
Proof. apply memory_pointer_sequence_normal with (operations:=operations); exact(affine_leaf_exact certificate). Qed.

Lemma affine_leaf_quiet source bounds lower upper layout scalars pointers operations
  (certificate:affine_leaf_certificate source bounds lower upper layout scalars pointers operations) :
  quiet_statement source=true.
Proof. apply memory_pointer_sequence_quiet with (operations:=operations); exact(affine_leaf_exact certificate). Qed.

Lemma affine_leaf_writes source bounds lower upper layout scalars pointers operations
  (certificate:affine_leaf_certificate source bounds lower upper layout scalars pointers operations) :
  writes_only [] source.
Proof. apply memory_pointer_sequence_writes with (operations:=operations); exact(affine_leaf_exact certificate). Qed.

Theorem affine_leaf_real_memory_decode source bounds lower upper layout scalars pointers operations
  (certificate:affine_leaf_certificate source bounds lower upper layout scalars pointers operations)
  fe ge locals valuation initial temps memory after final :
  interval_ranges bounds (map valuation layout) ->
  (forall identifier, In identifier (layout++scalars) -> temps!identifier=Some(Vint(Int.repr(valuation identifier)))) ->
  temp_agree pointers initial temps ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  memory_nary_sequence_point (map memory_nary_compute_instruction operations)
    (map valuation (layout++scalars))
    (RuntimeState (window_multi_pointer_locations initial lower upper) memory)
    (RuntimeState (window_multi_pointer_locations initial lower upper) final) /\ after=temps.
Proof.
  intros RANGES WORDS POINTERS SOURCE.
  destruct certificate as [EXACT VALID COVERED UNIQUE].
  apply flatten_region_execution in SOURCE; rewrite EXACT in SOURCE.
  destruct (@window_sequence_tail_inverse bounds lower upper operations layout scalars fe ge locals valuation
    temps memory after final VALID RANGES WORDS SOURCE) as [PHYSICAL EXIT].
  assert (INITIAL:memory_multi_pointer_sequence_physical initial (map valuation (layout++scalars)) operations memory final).
  { eapply memory_multi_pointer_sequence_frame; [exact COVERED| |exact PHYSICAL].
    intros identifier MEMBER; symmetry; exact(POINTERS identifier MEMBER). }
  split; [|exact EXIT].
  rewrite map_app.
  apply (proj1 (@window_sequence_point_execution bounds lower upper layout scalars initial
    (map valuation layout) (map valuation scalars) operations VALID RANGES ltac:(apply length_map) memory final)).
  rewrite <-map_app; exact INITIAL.
Qed.
Print Assumptions check_affine_leaf.
Print Assumptions affine_leaf_real_memory_decode.
