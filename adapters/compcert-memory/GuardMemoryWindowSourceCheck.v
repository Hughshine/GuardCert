From Stdlib Require Import List ZArith Lia Bool.
From compcert.lib Require Import Maps Coqlib Integers.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightSyntaxEquality ClightStraightLine ClightCountedLoop ClightStructuredProgress.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryRecursiveSource GuardMemoryRecursiveSyntax GuardMemoryParamPointerSyntax
  GuardMemoryPointerSourceWords GuardMemorySourceParameters GuardMemoryMultiPointerComputeSyntax GuardMemoryMultiPointerIdentifiers
  GuardMemoryNaryCompute GuardMemoryPointerCompute GuardMemoryScalarPointerComputeSyntax GuardMemoryTripleSyntax.
From GuardMemory Require Import GuardMemoryWindowCheck GuardMemoryWindowSyntax GuardMemoryWindowCompute.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Definition check_window_source source (nest : memory_source_nest) (caps : list Z) (root_lower : Z) (parameters : list ident) (parameter_bounds : list (Z*Z)) (pointers : list ident) (lower upper : Z) (scalars : list ident) (operations : list memory_nary_compute)
  : option (window_source_certificate source nest caps root_lower parameters parameter_bounds pointers lower upper scalars operations).
Proof.
  destruct (statement_eq source (memory_nest_source nest)) as [SOURCE|]; [|exact None].
  destruct (list_eq_dec peq (memory_nest_iterators nest) []) as [|NONEMPTY]; [exact None|].
  destruct (memory_nest_shapes_check nest) eqn:SHAPES; [|exact None].
  destruct (memory_nest_fresh_check nest) eqn:FRESH; [|exact None].
  destruct (Nat.eqb (length caps) (length (memory_nest_iterators nest))) eqn:LEN; [|exact None].
  destruct (forallb (fun cap => (0 <? cap) && (cap <=? Int.max_signed)) caps) eqn:CAP; [|exact None].
  destruct (window_signed_check root_lower && (root_lower <? hd 1 caps)) eqn:ROOT; [|exact None].
  destruct (Nat.eqb (length parameter_bounds) (length parameters)) eqn:PLEN; [|exact None].
  destruct (forallb (fun bound => (fst bound <? snd bound) && window_signed_check (fst bound) && window_signed_check (snd bound-1)) parameter_bounds) eqn:PCAP; [|exact None].
  destruct (forallb (fun identifier => negb (existsb (Pos.eqb identifier) (memory_nest_iterators nest))) parameters) eqn:PSTABLE; [|exact None].
  destruct (memory_pointer_address_parameters_check parameters operations) eqn:PUSED; [|exact None].
  destruct ((lower <? upper) && window_signed_check lower && window_signed_check (upper-1) && (4*(upper-lower) <=? Ptrofs.modulus)) eqn:EXTENT; [|exact None].
  destruct (forallb (fun identifier => negb (existsb (Pos.eqb identifier) (memory_nest_iterators nest))) pointers) eqn:POINTER; [|exact None].
  destruct (forallb (fun operation => memory_multi_pointer_operation_covered_check pointers operation) operations) eqn:COVER; [|exact None].
  destruct (memory_identifiers_unique_check ((memory_nest_iterators nest++parameters)++scalars)) eqn:UNIQUE; [|exact None].
  destruct (forallb (fun identifier => negb (existsb (Pos.eqb identifier) (memory_nest_iterators nest))) scalars) eqn:STABLE; [|exact None].
  destruct (memory_scalar_pointer_registers_check (memory_nest_iterators nest++parameters) scalars operations) eqn:USED; [|exact None].
  destruct (list_eq_dec memory_instruction_eq_dec (map memory_nary_compute_instruction operations) []) as [EMPTY|NONEMPTY_OPS];
    [destruct operations; [exact None|discriminate EMPTY]|].
  destruct (list_eq_dec statement_eq (flatten_region (memory_nest_leaf nest)) (map memory_pointer_compute_statement operations)) as [BODY|]; [|exact None].
  destruct (forallb (window_compute_check (window_source_coordinate_bounds root_lower caps++parameter_bounds) lower upper (memory_nest_iterators nest++parameters) scalars) operations)
    eqn:REQUESTS; [|exact None].
  assert (LIMITS : Forall (fun cap => 0 < cap /\ signed_range cap) caps).
  { apply Forall_forall; intros cap MEMBER; apply forallb_forall with (x := cap) in CAP; [|exact MEMBER].
    apply andb_true_iff in CAP as [POS MAX]; apply Z.ltb_lt in POS; apply Z.leb_le in MAX;
    unfold signed_range; change Int.min_signed with (-2147483648); split; lia. }
  assert (ROOT_LOWER : signed_range root_lower /\ root_lower < hd 1 caps).
  { rewrite andb_true_iff,Z.ltb_lt in ROOT; destruct ROOT as [SIGNED RANGE].
    split; [apply window_signed_check_sound; exact SIGNED|exact RANGE]. }
  assert (PARAM_LIMITS : Forall (fun bound => fst bound < snd bound /\
    signed_range (fst bound) /\ signed_range (snd bound-1)) parameter_bounds).
  { apply Forall_forall; intros box MEMBER; apply forallb_forall with (x := box) in PCAP; [|exact MEMBER].
    rewrite !andb_true_iff,Z.ltb_lt in PCAP; destruct PCAP as [[RANGE LOW] HIGH].
    split; [exact RANGE|split; apply window_signed_check_sound; assumption]. }
  apply Nat.eqb_eq in LEN,PLEN.
  assert (PARAM_STABLE : forall identifier, In identifier parameters -> ~ In identifier (memory_nest_iterators nest)).
  { intros identifier MEMBER BAD; apply forallb_forall with (x := identifier) in PSTABLE; [|exact MEMBER].
    apply negb_true_iff in PSTABLE; assert (FOUND : existsb (Pos.eqb identifier) (memory_nest_iterators nest) = true).
    { apply existsb_exists; exists identifier; split; [exact BAD|apply Pos.eqb_refl]. } congruence. }
  pose proof (@memory_pointer_address_parameters_check_sound parameters operations PUSED) as PARAM_USED.
  assert (WINDOW : lower < upper /\ signed_range lower /\ signed_range (upper-1) /\ 4*(upper-lower) <= Ptrofs.modulus).
  { rewrite !andb_true_iff,Z.ltb_lt,Z.leb_le in EXTENT; destruct EXTENT as [[[RANGE LOW] HIGH] WIDTH].
    split; [exact RANGE|split; [apply window_signed_check_sound; exact LOW|]].
    split; [apply window_signed_check_sound; exact HIGH|exact WIDTH]. }
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
  assert (CERT : Forall (window_compute_valid (window_source_coordinate_bounds root_lower caps++parameter_bounds) lower upper (memory_nest_iterators nest++parameters) scalars) operations).
  { apply Forall_forall; intros operation MEMBER; apply window_compute_check_sound.
    apply forallb_forall with (x := operation) in REQUESTS; assumption. }
  exact (Some (@WindowSourceCertificate source nest caps root_lower parameters parameter_bounds pointers lower upper scalars operations
    SOURCE NONEMPTY (@memory_nest_shapes_check_sound nest SHAPES) (@memory_nest_fresh_check_sound nest FRESH)
    LEN LIMITS ROOT_LOWER PLEN PARAM_LIMITS PARAM_STABLE PARAM_USED WINDOW PROTECTED
    (@memory_identifiers_unique_check_sound _ UNIQUE) SCALAR_STABLE SCALAR_USED OPS CERT COVERED BODY)).
Defined.
Print Assumptions check_window_source.
