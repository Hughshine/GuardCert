From Stdlib Require Import List ZArith Lia Bool.
From compcert.lib Require Import Maps Coqlib Integers.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightSyntaxEquality ClightStraightLine ClightCountedLoop ClightStructuredProgress.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryNaryCompute GuardMemoryPointerCompute GuardMemoryPointerComputeSyntax
  GuardMemoryPointerSequence GuardMemoryRecursiveSource GuardMemoryRecursiveSyntax GuardMemoryTripleSyntax GuardMemoryNaryAffineAccess.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Record memory_pointer_region_certificate source nest cap pointer extent operations := MemoryPointerRegionCertificate {
  pointer_region_source : source = memory_nest_source nest;
  pointer_region_nonempty : memory_nest_iterators nest <> [];
  pointer_region_shapes : memory_nest_shapes nest;
  pointer_region_fresh : memory_nest_fresh nest;
  pointer_region_cap : 0 < cap /\ signed_range cap;
  pointer_region_extent : 0 < extent /\ extent <= Int.max_signed+1 /\ 4*extent <= Ptrofs.modulus;
  pointer_region_protected : ~ In pointer (memory_nest_iterators nest);
  pointer_region_operations_nonempty : operations <> [];
  pointer_region_operations : Forall (memory_pointer_compute_valid (memory_recursive_limits nest cap)
    (memory_nest_iterators nest) pointer extent) operations;
  pointer_region_body : flatten_region (memory_nest_leaf nest) = map memory_pointer_compute_statement operations
}.
Record memory_pointer_region_package source := MemoryPointerRegionPackage {
  pointer_region_nest : memory_source_nest;
  pointer_region_limit : Z;
  pointer_region_pointer : ident;
  pointer_region_window : Z;
  pointer_region_code : list memory_nary_compute;
  pointer_region_syntax : memory_pointer_region_certificate source pointer_region_nest pointer_region_limit
    pointer_region_pointer pointer_region_window pointer_region_code
}.
Definition memory_pointer_region_instructions source (package : memory_pointer_region_package source) :=
  map memory_nary_compute_instruction (pointer_region_code package).
Definition check_memory_pointer_region source (nest : memory_source_nest) (cap : Z) (pointer : ident) (extent : Z) (operations : list memory_nary_compute)
  : option (memory_pointer_region_package source).
Proof.
  destruct (statement_eq source (memory_nest_source nest)) as [SOURCE|]; [|exact None].
  destruct (list_eq_dec peq (memory_nest_iterators nest) []) as [|NONEMPTY]; [exact None|].
  destruct (memory_nest_shapes_check nest) eqn:SHAPES; [|exact None].
  destruct (memory_nest_fresh_check nest) eqn:FRESH; [|exact None].
  destruct ((0 <? cap) && (cap <=? Int.max_signed)) eqn:CAP; [|exact None].
  destruct ((0 <? extent) && (extent <=? Int.max_signed+1) && (4*extent <=? Ptrofs.modulus)) eqn:EXTENT; [|exact None].
  destruct (existsb (Pos.eqb pointer) (memory_nest_iterators nest)) eqn:POINTER; [exact None|].
  destruct (list_eq_dec memory_instruction_eq_dec (map memory_nary_compute_instruction operations) []) as [EMPTY|NONEMPTY_OPS];
    [destruct operations; [exact None|discriminate EMPTY]|].
  destruct (list_eq_dec statement_eq (flatten_region (memory_nest_leaf nest)) (map memory_pointer_compute_statement operations)) as [BODY|]; [|exact None].
  destruct (forallb (memory_pointer_compute_check (memory_recursive_limits nest cap) (memory_nest_iterators nest) pointer extent) operations)
    eqn:REQUESTS; [|exact None].
  assert (LIMIT : 0 < cap /\ signed_range cap).
  { apply andb_true_iff in CAP as [POS MAX]; apply Z.ltb_lt in POS; apply Z.leb_le in MAX;
    unfold signed_range; change Int.min_signed with (-2147483648); split; lia. }
  assert (WINDOW : 0 < extent /\ extent <= Int.max_signed+1 /\ 4*extent <= Ptrofs.modulus).
  { rewrite !andb_true_iff,Z.ltb_lt,!Z.leb_le in EXTENT; tauto. }
  assert (PROTECTED : ~ In pointer (memory_nest_iterators nest)).
  { intro MEMBER; assert (FOUND : existsb (Pos.eqb pointer) (memory_nest_iterators nest) = true).
    { apply existsb_exists; exists pointer; split; [exact MEMBER|apply Pos.eqb_refl]. } congruence. }
  assert (OPS : operations <> []).
  { intro EMPTY; subst; apply NONEMPTY_OPS; reflexivity. }
  assert (CERT : Forall (memory_pointer_compute_valid (memory_recursive_limits nest cap) (memory_nest_iterators nest) pointer extent) operations).
  { apply Forall_forall; intros operation MEMBER; apply memory_pointer_compute_check_sound.
    apply forallb_forall with (x := operation) in REQUESTS; assumption. }
  exact (Some (@MemoryPointerRegionPackage source nest cap pointer extent operations
    (@MemoryPointerRegionCertificate source nest cap pointer extent operations SOURCE NONEMPTY
      (@memory_nest_shapes_check_sound nest SHAPES) (@memory_nest_fresh_check_sound nest FRESH)
      LIMIT WINDOW PROTECTED OPS CERT BODY))).
Defined.
Definition describe_memory_pointer_region_with_cap requested source :=
  let nest := propose_memory_source_nest (progress_syntax_size source) source in
  let extent := 1024 in
  match propose_memory_pointer_computes extent (memory_nest_iterators nest) (flatten_region (memory_nest_leaf nest)) with
  | Some (operation::operations) => check_memory_pointer_region source nest (Z.min requested (propose_memory_triple_cap (operation::operations)))
      (memory_nary_access_array (memory_nary_compute_write operation)) extent (operation::operations)
  | _ => None end.
Definition describe_memory_pointer_region := describe_memory_pointer_region_with_cap Int.max_signed.
Print Assumptions check_memory_pointer_region.
