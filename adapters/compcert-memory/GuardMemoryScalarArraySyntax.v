From Stdlib Require Import List ZArith Lia Bool.
From compcert.lib Require Import Maps Coqlib Integers.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightSyntaxEquality ClightStraightLine ClightCountedLoop ClightStructuredProgress.
From GuardMemory Require Import GuardMemoryNaryCompute GuardMemoryNarySequence GuardMemoryLayoutRegistry
  GuardMemoryRecursiveSource GuardMemoryRecursiveSyntax GuardMemoryTripleSyntax GuardMemorySourceParameters
  GuardMemoryScalarArrayCompute GuardMemoryScalarArrayComputeSyntax GuardMemoryScalarPointerComputeSyntax.
From GuardMemory Require Import GuardMemoryInstructionPadding.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Record memory_scalar_array_region_certificate source nest cap scalars operations := MemoryScalarArrayRegionCertificate {
  scalar_array_region_source : source = memory_nest_source nest;
  scalar_array_region_nonempty : memory_nest_iterators nest <> [];
  scalar_array_region_shapes : memory_nest_shapes nest;
  scalar_array_region_fresh : memory_nest_fresh nest;
  scalar_array_region_cap : 0 < cap /\ signed_range cap;
  scalar_array_region_registers : NoDup (memory_nest_iterators nest++scalars);
  scalar_array_region_stable : forall identifier, In identifier scalars -> ~ In identifier (memory_nest_iterators nest);
  scalar_array_region_used : forall identifier, In identifier scalars -> exists operation index,
    In operation operations /\ nth_error (memory_nest_iterators nest++scalars) index = Some identifier /\
    In index (memory_source_parameter_positions (memory_nary_compute_value operation));
  scalar_array_region_operations_nonempty : operations <> [];
  scalar_array_region_operations : Forall (memory_scalar_array_compute_valid (memory_recursive_limits nest cap)
    (memory_nest_iterators nest) scalars) operations;
  scalar_array_region_body : flatten_region (memory_nest_leaf nest) = map memory_nary_compute_statement operations;
  scalar_array_region_coverage : memory_descriptors_cover (memory_unique_descriptors (memory_nary_compute_sequence_anchors operations))
    (memory_nary_compute_sequence_requests operations)
}.
Record memory_scalar_array_region_package source := MemoryScalarArrayRegionPackage {
  scalar_array_region_nest : memory_source_nest;
  scalar_array_region_limit : Z;
  scalar_array_region_scalars : list ident;
  scalar_array_region_code : list memory_nary_compute;
  scalar_array_region_syntax : memory_scalar_array_region_certificate source scalar_array_region_nest scalar_array_region_limit
    scalar_array_region_scalars scalar_array_region_code
}.
Definition memory_scalar_array_region_instructions source (package : memory_scalar_array_region_package source) :=
  memory_pad_instructions (length (scalar_array_region_scalars package))
    (map memory_nary_compute_instruction (scalar_array_region_code package)).
Definition memory_scalar_array_region_descriptors source (package : memory_scalar_array_region_package source) :=
  memory_unique_descriptors (memory_nary_compute_sequence_anchors (scalar_array_region_code package)).
Definition check_memory_scalar_array_region source (nest : memory_source_nest) (cap : Z) (scalars : list ident) (operations : list memory_nary_compute)
  : option (memory_scalar_array_region_package source).
Proof.
  destruct (statement_eq source (memory_nest_source nest)) as [SOURCE|]; [|exact None].
  destruct (list_eq_dec peq (memory_nest_iterators nest) []) as [|NONEMPTY]; [exact None|].
  destruct (memory_nest_shapes_check nest) eqn:SHAPES; [|exact None].
  destruct (memory_nest_fresh_check nest) eqn:FRESH; [|exact None].
  destruct ((0 <? cap) && (cap <=? Int.max_signed)) eqn:CAP; [|exact None].
  destruct (memory_identifiers_unique_check (memory_nest_iterators nest++scalars)) eqn:UNIQUE; [|exact None].
  destruct (forallb (fun identifier => negb (existsb (Pos.eqb identifier) (memory_nest_iterators nest))) scalars) eqn:STABLE; [|exact None].
  destruct (memory_scalar_pointer_registers_check (memory_nest_iterators nest) scalars operations) eqn:USED; [|exact None].
  destruct operations as [|operation operations]; [exact None|].
  destruct (list_eq_dec statement_eq (flatten_region (memory_nest_leaf nest)) (map memory_nary_compute_statement (operation::operations))) as [BODY|]; [|exact None].
  destruct (forallb (memory_scalar_array_compute_check (memory_recursive_limits nest cap) (memory_nest_iterators nest) scalars) (operation::operations)) eqn:REQUESTS; [|exact None].
  destruct (memory_descriptors_cover_check (memory_unique_descriptors (memory_nary_compute_sequence_anchors (operation::operations)))
    (memory_nary_compute_sequence_requests (operation::operations))) eqn:COVER; [|exact None].
  assert (LIMIT : 0 < cap /\ signed_range cap).
  { apply andb_true_iff in CAP as [POS MAX]; apply Z.ltb_lt in POS; apply Z.leb_le in MAX;
    unfold signed_range; change Int.min_signed with (-2147483648); split; lia. }
  assert (SCALAR_STABLE : forall identifier, In identifier scalars -> ~ In identifier (memory_nest_iterators nest)).
  { intros identifier MEMBER BAD; apply forallb_forall with (x := identifier) in STABLE; [|exact MEMBER].
    apply negb_true_iff in STABLE; assert (FOUND : existsb (Pos.eqb identifier) (memory_nest_iterators nest) = true).
    { apply existsb_exists; exists identifier; split; [exact BAD|apply Pos.eqb_refl]. } congruence. }
  assert (SCALAR_USED : forall identifier, In identifier scalars -> exists op index,
    In op (operation::operations) /\ nth_error (memory_nest_iterators nest++scalars) index = Some identifier /\
    In index (memory_source_parameter_positions (memory_nary_compute_value op)))
    by (apply memory_scalar_pointer_registers_check_sound; exact USED).
  assert (CERT : Forall (memory_scalar_array_compute_valid (memory_recursive_limits nest cap) (memory_nest_iterators nest) scalars) (operation::operations)).
  { apply Forall_forall; intros op MEMBER; apply memory_scalar_array_compute_check_sound.
    apply forallb_forall with (x := op) in REQUESTS; assumption. }
  exact (Some (@MemoryScalarArrayRegionPackage source nest cap scalars (operation::operations)
    (@MemoryScalarArrayRegionCertificate source nest cap scalars (operation::operations) SOURCE NONEMPTY
      (@memory_nest_shapes_check_sound nest SHAPES) (@memory_nest_fresh_check_sound nest FRESH) LIMIT
      (@memory_identifiers_unique_check_sound _ UNIQUE) SCALAR_STABLE SCALAR_USED ltac:(discriminate) CERT BODY
      (@memory_descriptors_cover_check_sound _ _ COVER)))).
Defined.
Definition describe_memory_scalar_array_region_with_cap requested source :=
  let nest := propose_memory_source_nest (progress_syntax_size source) source in
  let scalars := propose_memory_pointer_scalars (memory_nest_iterators nest) (flatten_region (memory_nest_leaf nest)) in
  match propose_memory_scalar_array_computes (memory_nest_iterators nest) scalars (flatten_region (memory_nest_leaf nest)) with
  | Some (operation::operations) => check_memory_scalar_array_region source nest
      (Z.min requested (propose_memory_triple_cap (operation::operations))) scalars (operation::operations)
  | _ => None end.
Definition describe_memory_scalar_array_region := describe_memory_scalar_array_region_with_cap Int.max_signed.
Print Assumptions check_memory_scalar_array_region.
