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

Record memory_vector_pointer_region_certificate source nest caps pointers extent scalars operations := MemoryVectorPointerRegionCertificate {
  vector_pointer_region_source : source = memory_nest_source nest;
  vector_pointer_region_nonempty : memory_nest_iterators nest <> [];
  vector_pointer_region_shapes : memory_nest_shapes nest;
  vector_pointer_region_fresh : memory_nest_fresh nest;
  vector_pointer_region_limits_length : length caps = length (memory_nest_iterators nest);
  vector_pointer_region_caps : Forall (fun cap => 0 < cap /\ signed_range cap) caps;
  vector_pointer_region_extent : 0 < extent /\ extent <= Int.max_signed+1 /\ 4*extent <= Ptrofs.modulus;
  vector_pointer_region_protected : forall identifier, In identifier pointers -> ~ In identifier (memory_nest_iterators nest);
  vector_pointer_region_registers : NoDup (memory_nest_iterators nest++scalars);
  vector_pointer_region_stable : forall identifier, In identifier scalars -> ~ In identifier (memory_nest_iterators nest);
  vector_pointer_region_used : forall identifier, In identifier scalars -> exists operation index,
    In operation operations /\ nth_error (memory_nest_iterators nest++scalars) index = Some identifier /\
    In index (memory_source_parameter_positions (memory_nary_compute_value operation));
  vector_pointer_region_operations_nonempty : operations <> [];
  vector_pointer_region_operations : Forall (memory_multi_pointer_compute_valid caps
    (memory_nest_iterators nest) scalars extent) operations;
  vector_pointer_region_covered : Forall (memory_multi_pointer_operation_covered pointers) operations;
  vector_pointer_region_body : flatten_region (memory_nest_leaf nest) = map memory_pointer_compute_statement operations
}.
Record memory_vector_pointer_region_package source := MemoryVectorPointerRegionPackage {
  vector_pointer_region_nest : memory_source_nest;
  vector_pointer_region_limits : list Z;
  vector_pointer_region_pointers : list ident;
  vector_pointer_region_window : Z;
  vector_pointer_region_scalars : list ident;
  vector_pointer_region_code : list memory_nary_compute;
  vector_pointer_region_syntax : memory_vector_pointer_region_certificate source vector_pointer_region_nest vector_pointer_region_limits
    vector_pointer_region_pointers vector_pointer_region_window vector_pointer_region_scalars vector_pointer_region_code
}.
Definition memory_vector_pointer_region_instructions source (package : memory_vector_pointer_region_package source) :=
  memory_pad_instructions (length (vector_pointer_region_scalars package))
    (map memory_nary_compute_instruction (vector_pointer_region_code package)).
Definition check_memory_vector_pointer_region source (nest : memory_source_nest) (caps : list Z) (pointers : list ident) (extent : Z) (scalars : list ident) (operations : list memory_nary_compute)
  : option (memory_vector_pointer_region_package source).
Proof.
  destruct (statement_eq source (memory_nest_source nest)) as [SOURCE|]; [|exact None].
  destruct (list_eq_dec peq (memory_nest_iterators nest) []) as [|NONEMPTY]; [exact None|].
  destruct (memory_nest_shapes_check nest) eqn:SHAPES; [|exact None].
  destruct (memory_nest_fresh_check nest) eqn:FRESH; [|exact None].
  destruct (Nat.eqb (length caps) (length (memory_nest_iterators nest))) eqn:LEN; [|exact None].
  destruct (forallb (fun cap => (0 <? cap) && (cap <=? Int.max_signed)) caps) eqn:CAP; [|exact None].
  destruct ((0 <? extent) && (extent <=? Int.max_signed+1) && (4*extent <=? Ptrofs.modulus)) eqn:EXTENT; [|exact None].
  destruct (forallb (fun identifier => negb (existsb (Pos.eqb identifier) (memory_nest_iterators nest))) pointers) eqn:POINTER; [|exact None].
  destruct (forallb (fun operation => memory_multi_pointer_operation_covered_check pointers operation) operations) eqn:COVER; [|exact None].
  destruct (memory_identifiers_unique_check (memory_nest_iterators nest++scalars)) eqn:UNIQUE; [|exact None].
  destruct (forallb (fun identifier => negb (existsb (Pos.eqb identifier) (memory_nest_iterators nest))) scalars) eqn:STABLE; [|exact None].
  destruct (memory_scalar_pointer_registers_check (memory_nest_iterators nest) scalars operations) eqn:USED; [|exact None].
  destruct (list_eq_dec memory_instruction_eq_dec (map memory_nary_compute_instruction operations) []) as [EMPTY|NONEMPTY_OPS];
    [destruct operations; [exact None|discriminate EMPTY]|].
  destruct (list_eq_dec statement_eq (flatten_region (memory_nest_leaf nest)) (map memory_pointer_compute_statement operations)) as [BODY|]; [|exact None].
  destruct (forallb (memory_multi_pointer_compute_check caps (memory_nest_iterators nest) scalars extent) operations)
    eqn:REQUESTS; [|exact None].
  assert (LIMITS : Forall (fun cap => 0 < cap /\ signed_range cap) caps).
  { apply Forall_forall; intros cap MEMBER; apply forallb_forall with (x := cap) in CAP; [|exact MEMBER].
    apply andb_true_iff in CAP as [POS MAX]; apply Z.ltb_lt in POS; apply Z.leb_le in MAX;
    unfold signed_range; change Int.min_signed with (-2147483648); split; lia. }
  apply Nat.eqb_eq in LEN.
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
  assert (CERT : Forall (memory_multi_pointer_compute_valid caps (memory_nest_iterators nest) scalars extent) operations).
  { apply Forall_forall; intros operation MEMBER; apply memory_multi_pointer_compute_check_sound.
    apply forallb_forall with (x := operation) in REQUESTS; assumption. }
  exact (Some (@MemoryVectorPointerRegionPackage source nest caps pointers extent scalars operations
    (@MemoryVectorPointerRegionCertificate source nest caps pointers extent scalars operations SOURCE NONEMPTY
      (@memory_nest_shapes_check_sound nest SHAPES) (@memory_nest_fresh_check_sound nest FRESH)
      LEN LIMITS WINDOW PROTECTED (@memory_identifiers_unique_check_sound _ UNIQUE) SCALAR_STABLE SCALAR_USED OPS CERT COVERED BODY))).
Defined.
Print Assumptions check_memory_vector_pointer_region.
