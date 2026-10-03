From Stdlib Require Import List ZArith Lia Bool.
From compcert.lib Require Import Maps Coqlib Integers.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightSyntaxEquality ClightStraightLine ClightCountedLoop ClightStructuredProgress.
From GuardMemory Require Import GuardMemorySourceParameters GuardMemoryMultiPointerCompute GuardMemoryMultiPointerComputeSyntax GuardMemoryScalarPointerComputeSyntax GuardMemoryPointerSequence GuardMemoryInstr GuardMemoryNaryCompute GuardMemoryPointerCompute GuardMemoryPointerComputeSyntax
  GuardMemoryPointerSequence GuardMemoryRecursiveSource GuardMemoryRecursiveSyntax GuardMemoryTripleSyntax GuardMemoryNaryAffineAccess.
From GuardMemory Require Import GuardMemoryInstructionPadding GuardMemoryMultiPointerSequence GuardMemoryMultiPointerIdentifiers.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Record memory_multi_pointer_region_certificate source nest cap pointers extent scalars operations := MemoryMultiPointerRegionCertificate {
  multi_pointer_region_source : source = memory_nest_source nest;
  multi_pointer_region_nonempty : memory_nest_iterators nest <> [];
  multi_pointer_region_shapes : memory_nest_shapes nest;
  multi_pointer_region_fresh : memory_nest_fresh nest;
  multi_pointer_region_cap : 0 < cap /\ signed_range cap;
  multi_pointer_region_extent : 0 < extent /\ extent <= Int.max_signed+1 /\ 4*extent <= Ptrofs.modulus;
  multi_pointer_region_protected : forall identifier, In identifier pointers -> ~ In identifier (memory_nest_iterators nest);
  multi_pointer_region_registers : NoDup (memory_nest_iterators nest++scalars);
  multi_pointer_region_stable : forall identifier, In identifier scalars -> ~ In identifier (memory_nest_iterators nest);
  multi_pointer_region_used : forall identifier, In identifier scalars -> exists operation index,
    In operation operations /\ nth_error (memory_nest_iterators nest++scalars) index = Some identifier /\
    In index (memory_source_parameter_positions (memory_nary_compute_value operation));
  multi_pointer_region_operations_nonempty : operations <> [];
  multi_pointer_region_operations : Forall (memory_multi_pointer_compute_valid (memory_recursive_limits nest cap)
    (memory_nest_iterators nest) scalars extent) operations;
  multi_pointer_region_covered : Forall (memory_multi_pointer_operation_covered pointers) operations;
  multi_pointer_region_body : flatten_region (memory_nest_leaf nest) = map memory_pointer_compute_statement operations
}.
Record memory_multi_pointer_region_package source := MemoryMultiPointerRegionPackage {
  multi_pointer_region_nest : memory_source_nest;
  multi_pointer_region_limit : Z;
  multi_pointer_region_pointers : list ident;
  multi_pointer_region_window : Z;
  multi_pointer_region_scalars : list ident;
  multi_pointer_region_code : list memory_nary_compute;
  multi_pointer_region_syntax : memory_multi_pointer_region_certificate source multi_pointer_region_nest multi_pointer_region_limit
    multi_pointer_region_pointers multi_pointer_region_window multi_pointer_region_scalars multi_pointer_region_code
}.
Definition memory_multi_pointer_region_instructions source (package : memory_multi_pointer_region_package source) :=
  memory_pad_instructions (length (multi_pointer_region_scalars package))
    (map memory_nary_compute_instruction (multi_pointer_region_code package)).
Definition check_memory_multi_pointer_region_with_resource (finite_guard : bool) source (nest : memory_source_nest) (cap : Z) (pointers : list ident) (extent : Z) (scalars : list ident) (operations : list memory_nary_compute)
  : option (memory_multi_pointer_region_package source).
Proof.
  destruct (negb finite_guard || (Z.pow cap (Z.of_nat (length (memory_nest_iterators nest))) *
    Z.of_nat (fold_right (fun operation total => S (length (memory_nary_compute_reads operation))+total)%nat 0%nat operations) <=? 64)) eqn:RESOURCE; [|exact None].
  destruct (statement_eq source (memory_nest_source nest)) as [SOURCE|]; [|exact None].
  destruct (list_eq_dec peq (memory_nest_iterators nest) []) as [|NONEMPTY]; [exact None|].
  destruct (memory_nest_shapes_check nest) eqn:SHAPES; [|exact None].
  destruct (memory_nest_fresh_check nest) eqn:FRESH; [|exact None].
  destruct ((0 <? cap) && (cap <=? Int.max_signed)) eqn:CAP; [|exact None].
  destruct ((0 <? extent) && (extent <=? Int.max_signed+1) && (4*extent <=? Ptrofs.modulus)) eqn:EXTENT; [|exact None].
  destruct (forallb (fun identifier => negb (existsb (Pos.eqb identifier) (memory_nest_iterators nest))) pointers) eqn:POINTER; [|exact None].
  destruct (forallb (fun operation => memory_multi_pointer_operation_covered_check pointers operation) operations) eqn:COVER; [|exact None].
  destruct (memory_identifiers_unique_check (memory_nest_iterators nest++scalars)) eqn:UNIQUE; [|exact None].
  destruct (forallb (fun identifier => negb (existsb (Pos.eqb identifier) (memory_nest_iterators nest))) scalars) eqn:STABLE; [|exact None].
  destruct (memory_scalar_pointer_registers_check (memory_nest_iterators nest) scalars operations) eqn:USED; [|exact None].
  destruct (list_eq_dec memory_instruction_eq_dec (map memory_nary_compute_instruction operations) []) as [EMPTY|NONEMPTY_OPS];
    [destruct operations; [exact None|discriminate EMPTY]|].
  destruct (list_eq_dec statement_eq (flatten_region (memory_nest_leaf nest)) (map memory_pointer_compute_statement operations)) as [BODY|]; [|exact None].
  destruct (forallb (memory_multi_pointer_compute_check (memory_recursive_limits nest cap) (memory_nest_iterators nest) scalars extent) operations)
    eqn:REQUESTS; [|exact None].
  assert (LIMIT : 0 < cap /\ signed_range cap).
  { apply andb_true_iff in CAP as [POS MAX]; apply Z.ltb_lt in POS; apply Z.leb_le in MAX;
    unfold signed_range; change Int.min_signed with (-2147483648); split; lia. }
  assert (WINDOW : 0 < extent /\ extent <= Int.max_signed+1 /\ 4*extent <= Ptrofs.modulus).
  { rewrite !andb_true_iff,Z.ltb_lt,!Z.leb_le in EXTENT; tauto. }
  assert (PROTECTED : forall identifier, In identifier pointers -> ~ In identifier (memory_nest_iterators nest)).
  { intros identifier MEMBER BAD; apply forallb_forall with (x := identifier) in POINTER; [|exact MEMBER].
    apply negb_true_iff in POINTER; assert (FOUND : existsb (Pos.eqb identifier) (memory_nest_iterators nest) = true).
    { apply existsb_exists; exists identifier; split; [exact BAD|apply Pos.eqb_refl]. } congruence. }
  assert (COVERED : Forall (memory_multi_pointer_operation_covered pointers) operations).
  { apply Forall_forall; intros operation MEMBER; apply memory_multi_pointer_operation_covered_check_sound.
    apply forallb_forall with (x := operation) in COVER; assumption. }
  assert (SCALAR_STABLE : forall identifier, In identifier scalars -> ~ In identifier (memory_nest_iterators nest)).
  { intros identifier MEMBER BAD; apply forallb_forall with (x := identifier) in STABLE; [|exact MEMBER].
    apply negb_true_iff in STABLE; assert (FOUND : existsb (Pos.eqb identifier) (memory_nest_iterators nest) = true).
    { apply existsb_exists; exists identifier; split; [exact BAD|apply Pos.eqb_refl]. } congruence. }
  assert (SCALAR_USED : forall identifier, In identifier scalars -> exists operation index,
    In operation operations /\ nth_error (memory_nest_iterators nest++scalars) index = Some identifier /\
    In index (memory_source_parameter_positions (memory_nary_compute_value operation)))
    by (apply memory_scalar_pointer_registers_check_sound; exact USED).
  assert (OPS : operations <> []).
  { intro EMPTY; subst; apply NONEMPTY_OPS; reflexivity. }
  assert (CERT : Forall (memory_multi_pointer_compute_valid (memory_recursive_limits nest cap) (memory_nest_iterators nest) scalars extent) operations).
  { apply Forall_forall; intros operation MEMBER; apply memory_multi_pointer_compute_check_sound.
    apply forallb_forall with (x := operation) in REQUESTS; assumption. }
  exact (Some (@MemoryMultiPointerRegionPackage source nest cap pointers extent scalars operations
    (@MemoryMultiPointerRegionCertificate source nest cap pointers extent scalars operations SOURCE NONEMPTY
      (@memory_nest_shapes_check_sound nest SHAPES) (@memory_nest_fresh_check_sound nest FRESH)
      LIMIT WINDOW PROTECTED (@memory_identifiers_unique_check_sound _ UNIQUE) SCALAR_STABLE SCALAR_USED OPS CERT COVERED BODY))).
Defined.
Definition check_memory_multi_pointer_region := check_memory_multi_pointer_region_with_resource true.
Definition describe_memory_multi_pointer_region_with_cap requested source :=
  let nest := propose_memory_source_nest (progress_syntax_size source) source in
  let extent := 1024 in
  let scalars := propose_memory_pointer_scalars (memory_nest_iterators nest) (flatten_region (memory_nest_leaf nest)) in
  match propose_memory_scalar_pointer_computes extent (memory_nest_iterators nest) scalars (flatten_region (memory_nest_leaf nest)) with
  | Some (operation::operations) => check_memory_multi_pointer_region source nest (Z.min requested (propose_memory_triple_cap (operation::operations)))
      (memory_multi_pointer_operation_identifiers (operation::operations)) extent scalars (operation::operations)
  | _ => None end.
Fixpoint describe_memory_multi_pointer_caps caps source := match caps with
  | [] => None
  | cap::rest => match describe_memory_multi_pointer_region_with_cap cap source with
      | Some package => Some package | None => describe_memory_multi_pointer_caps rest source end end.
Definition describe_memory_multi_pointer_region := describe_memory_multi_pointer_caps [8;4;3;2;1].
Print Assumptions check_memory_multi_pointer_region.
