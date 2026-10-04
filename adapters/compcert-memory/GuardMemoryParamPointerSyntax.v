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
From GuardMemory Require Import GuardMemoryPointerSourceWords.
Definition memory_pointer_address_parameters_check parameters operations :=
  forallb (fun identifier => existsb (fun operation =>
    existsb (Pos.eqb identifier) (memory_pointer_operation_address_reads operation)) operations) parameters.
Lemma memory_pointer_address_parameters_check_sound parameters operations :
  memory_pointer_address_parameters_check parameters operations = true ->
  forall identifier, In identifier parameters -> exists operation,
    In operation operations /\ In identifier (memory_pointer_operation_address_reads operation).
Proof.
  unfold memory_pointer_address_parameters_check; intros CHECK identifier MEMBER.
  apply forallb_forall with (x := identifier) in CHECK; [|exact MEMBER].
  apply existsb_exists in CHECK as [operation [IN USED]].
  apply existsb_exists in USED as [same [USED SAME]]; apply Pos.eqb_eq in SAME; subst.
  exists operation; auto.
Qed.

Record memory_param_pointer_region_certificate source nest caps parameters parameter_caps pointers extent scalars operations := MemoryParamPointerRegionCertificate {
  param_pointer_region_source : source = memory_nest_source nest;
  param_pointer_region_nonempty : memory_nest_iterators nest <> [];
  param_pointer_region_shapes : memory_nest_shapes nest;
  param_pointer_region_fresh : memory_nest_fresh nest;
  param_pointer_region_limits_length : length caps = length (memory_nest_iterators nest);
  param_pointer_region_caps : Forall (fun cap => 0 < cap /\ signed_range cap) caps;
  param_pointer_region_parameter_limits_length : length parameter_caps = length parameters;
  param_pointer_region_parameter_caps : Forall (fun cap => 0 < cap /\ signed_range cap) parameter_caps;
  param_pointer_region_parameter_stable : forall identifier, In identifier parameters -> ~ In identifier (memory_nest_iterators nest);
  param_pointer_region_parameter_used : forall identifier, In identifier parameters -> exists operation,
    In operation operations /\ In identifier (memory_pointer_operation_address_reads operation);
  param_pointer_region_extent : 0 < extent /\ extent <= Int.max_signed+1 /\ 4*extent <= Ptrofs.modulus;
  param_pointer_region_protected : forall identifier, In identifier pointers -> ~ In identifier (memory_nest_iterators nest);
  param_pointer_region_registers : NoDup ((memory_nest_iterators nest++parameters)++scalars);
  param_pointer_region_stable : forall identifier, In identifier scalars -> ~ In identifier (memory_nest_iterators nest);
  param_pointer_region_used : forall identifier, In identifier scalars -> exists operation index,
    In operation operations /\ nth_error ((memory_nest_iterators nest++parameters)++scalars) index = Some identifier /\
    In index (memory_source_parameter_positions (memory_nary_compute_value operation));
  param_pointer_region_operations_nonempty : operations <> [];
  param_pointer_region_operations : Forall (memory_multi_pointer_compute_valid (caps++parameter_caps)
    (memory_nest_iterators nest++parameters) scalars extent) operations;
  param_pointer_region_covered : Forall (memory_multi_pointer_operation_covered pointers) operations;
  param_pointer_region_body : flatten_region (memory_nest_leaf nest) = map memory_pointer_compute_statement operations
}.
Record memory_param_pointer_region_package source := MemoryParamPointerRegionPackage {
  param_pointer_region_nest : memory_source_nest;
  param_pointer_region_limits : list Z;
  param_pointer_region_parameters : list ident;
  param_pointer_region_parameter_limits : list Z;
  param_pointer_region_pointers : list ident;
  param_pointer_region_window : Z;
  param_pointer_region_scalars : list ident;
  param_pointer_region_code : list memory_nary_compute;
  param_pointer_region_syntax : memory_param_pointer_region_certificate source param_pointer_region_nest param_pointer_region_limits param_pointer_region_parameters param_pointer_region_parameter_limits
    param_pointer_region_pointers param_pointer_region_window param_pointer_region_scalars param_pointer_region_code
}.
Definition memory_param_pointer_region_instructions source (package : memory_param_pointer_region_package source) :=
  memory_pad_instructions (length (param_pointer_region_scalars package))
    (map memory_nary_compute_instruction (param_pointer_region_code package)).
Definition check_memory_param_pointer_region source (nest : memory_source_nest) (caps : list Z) (parameters : list ident) (parameter_caps : list Z) (pointers : list ident) (extent : Z) (scalars : list ident) (operations : list memory_nary_compute)
  : option (memory_param_pointer_region_package source).
Proof.
  destruct (statement_eq source (memory_nest_source nest)) as [SOURCE|]; [|exact None].
  destruct (list_eq_dec peq (memory_nest_iterators nest) []) as [|NONEMPTY]; [exact None|].
  destruct (memory_nest_shapes_check nest) eqn:SHAPES; [|exact None].
  destruct (memory_nest_fresh_check nest) eqn:FRESH; [|exact None].
  destruct (Nat.eqb (length caps) (length (memory_nest_iterators nest))) eqn:LEN; [|exact None].
  destruct (forallb (fun cap => (0 <? cap) && (cap <=? Int.max_signed)) caps) eqn:CAP; [|exact None].
  destruct (Nat.eqb (length parameter_caps) (length parameters)) eqn:PLEN; [|exact None].
  destruct (forallb (fun cap => (0 <? cap) && (cap <=? Int.max_signed)) parameter_caps) eqn:PCAP; [|exact None].
  destruct (forallb (fun identifier => negb (existsb (Pos.eqb identifier) (memory_nest_iterators nest))) parameters) eqn:PSTABLE; [|exact None].
  destruct (memory_pointer_address_parameters_check parameters operations) eqn:PUSED; [|exact None].
  destruct ((0 <? extent) && (extent <=? Int.max_signed+1) && (4*extent <=? Ptrofs.modulus)) eqn:EXTENT; [|exact None].
  destruct (forallb (fun identifier => negb (existsb (Pos.eqb identifier) (memory_nest_iterators nest))) pointers) eqn:POINTER; [|exact None].
  destruct (forallb (fun operation => memory_multi_pointer_operation_covered_check pointers operation) operations) eqn:COVER; [|exact None].
  destruct (memory_identifiers_unique_check ((memory_nest_iterators nest++parameters)++scalars)) eqn:UNIQUE; [|exact None].
  destruct (forallb (fun identifier => negb (existsb (Pos.eqb identifier) (memory_nest_iterators nest))) scalars) eqn:STABLE; [|exact None].
  destruct (memory_scalar_pointer_registers_check (memory_nest_iterators nest++parameters) scalars operations) eqn:USED; [|exact None].
  destruct (list_eq_dec memory_instruction_eq_dec (map memory_nary_compute_instruction operations) []) as [EMPTY|NONEMPTY_OPS];
    [destruct operations; [exact None|discriminate EMPTY]|].
  destruct (list_eq_dec statement_eq (flatten_region (memory_nest_leaf nest)) (map memory_pointer_compute_statement operations)) as [BODY|]; [|exact None].
  destruct (forallb (memory_multi_pointer_compute_check (caps++parameter_caps) (memory_nest_iterators nest++parameters) scalars extent) operations)
    eqn:REQUESTS; [|exact None].
  assert (LIMITS : Forall (fun cap => 0 < cap /\ signed_range cap) caps).
  { apply Forall_forall; intros cap MEMBER; apply forallb_forall with (x := cap) in CAP; [|exact MEMBER].
    apply andb_true_iff in CAP as [POS MAX]; apply Z.ltb_lt in POS; apply Z.leb_le in MAX;
    unfold signed_range; change Int.min_signed with (-2147483648); split; lia. }
  assert (PARAM_LIMITS : Forall (fun cap => 0 < cap /\ signed_range cap) parameter_caps).
  { apply Forall_forall; intros cap MEMBER; apply forallb_forall with (x := cap) in PCAP; [|exact MEMBER].
    apply andb_true_iff in PCAP as [POS MAX]; apply Z.ltb_lt in POS; apply Z.leb_le in MAX;
    unfold signed_range; change Int.min_signed with (-2147483648); split; lia. }
  apply Nat.eqb_eq in LEN,PLEN.
  assert (PARAM_STABLE : forall identifier, In identifier parameters -> ~ In identifier (memory_nest_iterators nest)).
  { intros identifier MEMBER BAD; apply forallb_forall with (x := identifier) in PSTABLE; [|exact MEMBER].
    apply negb_true_iff in PSTABLE; assert (FOUND : existsb (Pos.eqb identifier) (memory_nest_iterators nest) = true).
    { apply existsb_exists; exists identifier; split; [exact BAD|apply Pos.eqb_refl]. } congruence. }
  pose proof (@memory_pointer_address_parameters_check_sound parameters operations PUSED) as PARAM_USED.
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
    In operation operations /\ nth_error ((memory_nest_iterators nest++parameters)++scalars) index = Some identifier /\
    In index (memory_source_parameter_positions (memory_nary_compute_value operation)))
    by (apply memory_scalar_pointer_registers_check_sound; exact USED).
  assert (OPS : operations <> []).
  { intro EMPTY; subst; apply NONEMPTY_OPS; reflexivity. }
  assert (CERT : Forall (memory_multi_pointer_compute_valid (caps++parameter_caps) (memory_nest_iterators nest++parameters) scalars extent) operations).
  { apply Forall_forall; intros operation MEMBER; apply memory_multi_pointer_compute_check_sound.
    apply forallb_forall with (x := operation) in REQUESTS; assumption. }
  exact (Some (@MemoryParamPointerRegionPackage source nest caps parameters parameter_caps pointers extent scalars operations
    (@MemoryParamPointerRegionCertificate source nest caps parameters parameter_caps pointers extent scalars operations SOURCE NONEMPTY
      (@memory_nest_shapes_check_sound nest SHAPES) (@memory_nest_fresh_check_sound nest FRESH)
      LEN LIMITS PLEN PARAM_LIMITS PARAM_STABLE PARAM_USED WINDOW PROTECTED (@memory_identifiers_unique_check_sound _ UNIQUE) SCALAR_STABLE SCALAR_USED OPS CERT COVERED BODY))).
Defined.
Print Assumptions check_memory_param_pointer_region.
