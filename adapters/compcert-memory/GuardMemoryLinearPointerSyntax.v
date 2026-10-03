From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Coqlib Integers.
From compcert.common Require Import AST Values.
From compcert.cfrontend Require Import Clight.
From polcert.src Require Import PolyBase.
From polcert.lib Require Import Linalg Misc.
From Guard Require Import ClightStructuredProgress ClightStraightLine ClightCountedLoop ClightNoWrap.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles
  GuardMemoryNaryCompute GuardMemoryNaryAffineAccess GuardMemoryNaryAffineExpressions GuardMemoryPointerSequence
  GuardMemoryScalarPointerComputeSyntax GuardMemoryTripleSyntax GuardMemoryRecursiveSource GuardMemoryRecursiveSyntax GuardMemoryRecursiveDomain
  GuardMemoryMultiPointerSyntax GuardMemoryMultiPointerIdentifiers GuardMemoryMultiPointerFootprint
  GuardMemoryMultiPointerProjectedCandidate GuardMemoryRectangularFootprint GuardMemoryInstructionPadding
  GuardMemoryFiniteFootprint GuardMemoryLoopTrace.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_linear_pointer_accesses operations :=
  flat_map (fun operation => memory_nary_compute_write operation::memory_nary_compute_reads operation) operations.
Definition memory_linear_pointer_identifiers operations :=
  map memory_nary_access_array (memory_linear_pointer_accesses operations).

Record memory_linear_pointer_package source := MemoryLinearPointerPackage {
  linear_pointer_region : memory_multi_pointer_region_package source;
  linear_pointer_bound : ident;
  linear_pointer_one_bound : memory_nest_bounds (multi_pointer_region_nest linear_pointer_region) = [linear_pointer_bound];
  linear_pointer_accesses_unit : Forall (fun access => memory_nary_access_index access = ([1],0))
    (memory_linear_pointer_accesses (multi_pointer_region_code linear_pointer_region))
}.

Definition check_memory_linear_pointer_package source (package : memory_multi_pointer_region_package source)
  : option (memory_linear_pointer_package source).
Proof.
  destruct (memory_nest_bounds (multi_pointer_region_nest package)) as [|bound [|second rest]] eqn:BOUNDS;
    [exact None| |exact None].
  destruct (forallb (fun access => if @List.list_eq_dec Z Z.eq_dec (fst (memory_nary_access_index access)) [1]
      then Z.eqb (snd (memory_nary_access_index access)) 0 else false)
    (memory_linear_pointer_accesses (multi_pointer_region_code package))) eqn:UNIT; [|exact None].
  assert (ACCESSES : Forall (fun access => memory_nary_access_index access = ([1],0))
    (memory_linear_pointer_accesses (multi_pointer_region_code package))).
  { apply Forall_forall; intros access MEMBER; apply forallb_forall with (x := access) in UNIT; [|exact MEMBER].
    destruct (@List.list_eq_dec Z Z.eq_dec (fst (memory_nary_access_index access)) [1]) as [FIRST|]; [|discriminate].
    apply Z.eqb_eq in UNIT; destruct (memory_nary_access_index access); cbn in *; subst; reflexivity. }
  exact (Some (@MemoryLinearPointerPackage source package bound BOUNDS ACCESSES)).
Defined.

Definition describe_memory_linear_pointer_region source :=
  let nest := propose_memory_source_nest (progress_syntax_size source) source in
  let extent := 1024 in
  let scalars := propose_memory_pointer_scalars (memory_nest_iterators nest) (flatten_region (memory_nest_leaf nest)) in
  match propose_memory_scalar_pointer_computes extent (memory_nest_iterators nest) scalars (flatten_region (memory_nest_leaf nest)) with
  | Some (operation::operations) =>
      match check_memory_multi_pointer_region_with_resource false source nest
        (Z.min extent (propose_memory_triple_cap (operation::operations)))
        (memory_multi_pointer_operation_identifiers (operation::operations)) extent scalars (operation::operations) with
      | Some package => check_memory_linear_pointer_package package | None => None end
  | _ => None end.

Lemma memory_linear_pointer_point_footprint extra operations index :
  Forall (fun access => memory_nary_access_index access = ([1],0)) (memory_linear_pointer_accesses operations) ->
  memory_point_footprint (memory_pad_instructions extra (map memory_nary_compute_instruction operations)) [index] =
    map (fun identifier => point_cell identifier index) (memory_linear_pointer_identifiers operations).
Proof.
  intro UNIT; unfold memory_linear_pointer_accesses in UNIT.
  induction operations as [|operation operations IH]; [reflexivity|].
  cbn [flat_map] in UNIT; apply Forall_app in UNIT as [HEAD REST]; inversion HEAD; subst.
  cbn [memory_point_footprint memory_pad_instructions map flat_map].
  rewrite memory_pad_instruction_footprint.
  change (memory_instruction_footprint (memory_nary_compute_instruction operation) [index] ++
    memory_point_footprint (memory_pad_instructions extra (map memory_nary_compute_instruction operations)) [index] =
      map (fun identifier => point_cell identifier index) (memory_linear_pointer_identifiers (operation::operations))).
  rewrite IH by exact REST.
  unfold memory_linear_pointer_identifiers,memory_linear_pointer_accesses.
  cbn [flat_map]; rewrite !map_app,!map_map; f_equal.
  unfold memory_instruction_footprint; cbn [memory_nary_compute_instruction instruction_write instruction_reads].
  rewrite map_map.
  change (map (fun access => exact_cell (memory_nary_access_instruction access) [index])
    (memory_nary_compute_write operation::memory_nary_compute_reads operation) =
    map (fun access => point_cell (memory_nary_access_array access) index)
    (memory_nary_compute_write operation::memory_nary_compute_reads operation)).
  apply map_ext_in; intros access MEMBER.
  apply Forall_forall with (x := access) in HEAD; [|exact MEMBER].
  rewrite memory_nary_access_cell,HEAD.
  unfold memory_nary_index_value; cbn [fst snd dot_product]; f_equal; ring.

Qed.

Theorem memory_linear_pointer_runtime_footprint source (package : memory_linear_pointer_package source) temps count :
  temps ! (linear_pointer_bound package) = Some (Vint (Int.repr count)) -> signed_range count ->
  memory_multi_pointer_runtime_footprint (linear_pointer_region package) temps =
    flat_map (fun index => map (fun identifier => point_cell identifier index)
      (memory_linear_pointer_identifiers (multi_pointer_region_code (linear_pointer_region package)))) (Zrange 0 count).
Proof.
  intros BOUND RANGE.
  assert (DIMENSIONS : length (memory_nest_iterators (multi_pointer_region_nest (linear_pointer_region package))) = 1%nat).
  { rewrite memory_nest_lengths,(linear_pointer_one_bound package); reflexivity. }
  pose proof (@memory_multi_pointer_source_footprint source (linear_pointer_region package) [count]
    (memory_recursive_parameters (multi_pointer_region_scalars (linear_pointer_region package)) temps)
    ltac:(cbn; symmetry; exact DIMENSIONS)) as FOOTPRINT.
  unfold memory_recursive_parameters,temp_word in FOOTPRINT.
  rewrite length_map in FOOTPRINT; cbn [length app] in FOOTPRINT.
  unfold memory_multi_pointer_runtime_footprint,memory_multi_pointer_runtime_context,memory_multi_pointer_runtime_loop.
  rewrite DIMENSIONS; unfold memory_recursive_parameters; rewrite map_app,(linear_pointer_one_bound package).
  cbn [map]; unfold temp_word; rewrite BOUND,Int.signed_repr by exact RANGE.
  cbn [app]; rewrite FOOTPRINT.
  cbn [memory_rectangular_points app].
  rewrite memory_flat_map_associative; apply memory_flat_map_ext_in; intros index MEMBER.
  cbn [flat_map app]; rewrite app_nil_r.
  unfold memory_multi_pointer_region_instructions; apply memory_linear_pointer_point_footprint;
    exact (linear_pointer_accesses_unit package).

Qed.

Theorem memory_linear_pointer_footprint_member source (package : memory_linear_pointer_package source) temps count cell :
  temps ! (linear_pointer_bound package) = Some (Vint (Int.repr count)) -> signed_range count ->
  (In cell (memory_multi_pointer_runtime_footprint (linear_pointer_region package) temps) <->
    exists identifier index,
      In identifier (memory_linear_pointer_identifiers (multi_pointer_region_code (linear_pointer_region package))) /\
      0 <= index < count /\ cell = point_cell identifier index).
Proof.
  intros BOUND RANGE; rewrite (@memory_linear_pointer_runtime_footprint source package temps count BOUND RANGE).
  rewrite in_flat_map; split.
  - intros [index [INDEX CELL]]; apply Zrange_in in INDEX; apply in_map_iff in CELL as [identifier [SAME MEMBER]].
    exists identifier,index; auto.
  - intros [identifier [index [MEMBER [INDEX ->]]]]; exists index; split;
      [apply Zrange_in; exact INDEX|apply in_map_iff; exists identifier; auto].
Qed.

Print Assumptions check_memory_linear_pointer_package.
Print Assumptions memory_linear_pointer_runtime_footprint.
