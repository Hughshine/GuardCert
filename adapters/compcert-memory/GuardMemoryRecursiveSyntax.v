From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Integers.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightSyntaxEquality ClightFrontendRegion ClightStraightLine
  ClightCountedLoop ClightStructuredProgress ClightRectangularLoops.
From GuardMemory Require Import GuardMemoryNaryCompute GuardMemoryNaryComputeSyntax
  GuardMemoryNarySequence GuardMemoryNaryBodyModel GuardMemoryLayoutRegistry GuardMemoryRecursiveSource
  GuardMemoryTripleSyntax.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint memory_identifiers_unique_check (identifiers : list ident) := match identifiers with
  | [] => true | identifier::rest => negb (existsb (Pos.eqb identifier) rest) && memory_identifiers_unique_check rest end.
Lemma memory_identifiers_unique_check_sound identifiers : memory_identifiers_unique_check identifiers = true -> NoDup identifiers.
Proof.
  induction identifiers; cbn; intro CHECK; [constructor|].
  rewrite andb_true_iff,negb_true_iff in CHECK; destruct CHECK as [FRESH REST].
  constructor; [|apply IHidentifiers; exact REST].
  intro MEMBER; assert (FOUND : existsb (Pos.eqb a) identifiers = true).
  { apply existsb_exists; exists a; split; [exact MEMBER|apply Pos.eqb_refl]. }
  congruence.
Qed.
Definition memory_nest_fresh_check nest := memory_identifiers_unique_check (memory_nest_iterators nest) &&
  forallb (fun iterator => negb (existsb (Pos.eqb iterator) (memory_nest_bounds nest))) (memory_nest_iterators nest).
Lemma memory_nest_fresh_check_sound nest : memory_nest_fresh_check nest = true -> memory_nest_fresh nest.
Proof.
  unfold memory_nest_fresh_check; rewrite andb_true_iff; intros [UNIQUE DISJOINT]; split.
  - apply memory_identifiers_unique_check_sound; exact UNIQUE.
  - intros identifier MEMBER BAD; apply forallb_forall with (x := identifier) in DISJOINT; [|exact MEMBER].
    apply negb_true_iff in DISJOINT; assert (FOUND : existsb (Pos.eqb identifier) (memory_nest_bounds nest) = true).
    { apply existsb_exists; exists identifier; split; [exact BAD|apply Pos.eqb_refl]. }
    congruence.
Qed.
Definition memory_nest_child_shape_check body child := match child with
  | MemorySourceLeaf code => if statement_eq body code then true else false
  | MemorySourceAxis iterator _ _ _ =>
      if list_eq_dec statement_eq (flatten_region body) [rectangle_reset iterator;memory_nest_source child]
        then true else false end.
Fixpoint memory_nest_shapes_check nest := match nest with
  | MemorySourceLeaf _ => true
  | MemorySourceAxis _ _ body child => memory_nest_child_shape_check body child && memory_nest_shapes_check child end.
Lemma memory_nest_shapes_check_sound nest : memory_nest_shapes_check nest = true -> memory_nest_shapes nest.
Proof.
  induction nest; cbn [memory_nest_shapes_check memory_nest_shapes]; intro CHECK; [exact I|].
  apply andb_true_iff in CHECK as [SHAPE REST]; split; [|apply IHnest; exact REST].
  destruct nest; cbn [memory_nest_child_shape_check] in SHAPE;
    repeat destruct statement_eq; repeat destruct list_eq_dec; try discriminate; assumption.
Qed.
Fixpoint propose_memory_source_nest fuel source : memory_source_nest := match fuel with
  | O => MemorySourceLeaf source
  | S remaining => match propose_frontend_shape source with
      | Some (iterator,bound,body) =>
          let child := match flatten_region body with
            | [Sset _ _;nested] => match propose_frontend_shape nested with
                | Some _ => propose_memory_source_nest remaining nested
                | None => MemorySourceLeaf body end
            | _ => MemorySourceLeaf body end in
          MemorySourceAxis iterator bound body child
      | None => MemorySourceLeaf source end end.
Definition memory_recursive_limits nest (cap : Z) := repeat cap (length (memory_nest_iterators nest)).
Record memory_recursive_region_certificate source nest cap := MemoryRecursiveRegionCertificate {
  recursive_region_source : source = memory_nest_source nest;
  recursive_region_nonempty : memory_nest_iterators nest <> [];
  recursive_region_shapes : memory_nest_shapes nest;
  recursive_region_fresh : memory_nest_fresh nest;
  recursive_region_cap : 0 < cap /\ signed_range cap;
  recursive_region_model : memory_nary_body_model (memory_recursive_limits nest cap)
    (memory_nest_iterators nest) (memory_nest_leaf nest)
}.
Record memory_recursive_region_package source := MemoryRecursiveRegionPackage {
  recursive_region_nest : memory_source_nest;
  recursive_region_limit : Z;
  recursive_region_syntax : memory_recursive_region_certificate source recursive_region_nest recursive_region_limit
}.
Definition memory_recursive_region_model source (package : memory_recursive_region_package source) := recursive_region_model (recursive_region_syntax package).
Definition memory_recursive_region_instructions source (package : memory_recursive_region_package source) := nary_body_instructions (memory_recursive_region_model package).
Definition memory_recursive_region_descriptors source (package : memory_recursive_region_package source) := nary_body_descriptors (memory_recursive_region_model package).
Definition check_memory_recursive_region source (nest : memory_source_nest) (cap : Z)
  (operations : list memory_nary_compute) : option (memory_recursive_region_package source).
Proof.
  destruct (statement_eq source (memory_nest_source nest)) as [SOURCE|]; [|exact None].
  destruct (list_eq_dec peq (memory_nest_iterators nest) []) as [|NONEMPTY]; [exact None|].
  destruct (memory_nest_shapes_check nest) eqn:SHAPES; [|exact None].
  destruct (memory_nest_fresh_check nest) eqn:FRESH; [|exact None].
  destruct ((0 <? cap) && (cap <=? Int.max_signed)) eqn:CAP; [|exact None].
  destruct (list_eq_dec statement_eq (flatten_region (memory_nest_leaf nest)) (map memory_nary_compute_statement operations)) as [BODY|]; [|exact None].
  destruct (forallb (memory_nary_compute_check (memory_recursive_limits nest cap) (memory_nest_iterators nest)) operations) eqn:REQUESTS; [|exact None].
  destruct (memory_descriptors_cover_check (memory_unique_descriptors (memory_nary_compute_sequence_anchors operations))
    (memory_nary_compute_sequence_requests operations)) eqn:COVER; [|exact None].
  assert (LIMIT : 0 < cap /\ signed_range cap).
  { apply andb_true_iff in CAP as [POS MAX]; apply Z.ltb_lt in POS; apply Z.leb_le in MAX;
    unfold signed_range; change Int.min_signed with (-2147483648); split; lia. }
  assert (CERT : Forall (memory_nary_compute_valid (memory_recursive_limits nest cap) (memory_nest_iterators nest)) operations).
  { apply Forall_forall; intros operation MEMBER; apply memory_nary_compute_check_sound.
    apply forallb_forall with (x := operation) in REQUESTS; assumption. }
  exact (Some (@MemoryRecursiveRegionPackage source nest cap
    (@MemoryRecursiveRegionCertificate source nest cap SOURCE NONEMPTY (@memory_nest_shapes_check_sound nest SHAPES)
      (@memory_nest_fresh_check_sound nest FRESH) LIMIT
      (@memory_nary_compute_body_model (memory_recursive_limits nest cap) operations (memory_nest_iterators nest)
        (memory_nest_leaf nest) CERT (@memory_descriptors_cover_check_sound _ _ COVER) BODY)))).
Defined.
Definition describe_memory_recursive_region source :=
  let nest := propose_memory_source_nest (progress_syntax_size source) source in
  match propose_memory_nary_computes (memory_nest_iterators nest) (flatten_region (memory_nest_leaf nest)) with
  | Some (operation::operations) => check_memory_recursive_region source nest
      (propose_memory_triple_cap (operation::operations)) (operation::operations)
  | _ => None end.
Print Assumptions check_memory_recursive_region.
