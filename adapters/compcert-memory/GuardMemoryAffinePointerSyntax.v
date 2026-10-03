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

From GuardMemory Require Import GuardMemoryLinearPointerSyntax GuardMemoryMultiPointerCompute GuardMemoryMultiPointerAccess.

Record memory_affine_pointer_package source := MemoryAffinePointerPackage {
  affine_pointer_region : memory_multi_pointer_region_package source;
  affine_pointer_bound : ident;
  affine_pointer_iterator : ident;
  affine_pointer_one_bound : memory_nest_bounds (multi_pointer_region_nest affine_pointer_region) = [affine_pointer_bound];
  affine_pointer_one_iterator : memory_nest_iterators (multi_pointer_region_nest affine_pointer_region) = [affine_pointer_iterator]
}.
Definition check_memory_affine_pointer_package source (package : memory_multi_pointer_region_package source)
  : option (memory_affine_pointer_package source).
Proof.
  destruct (memory_nest_bounds (multi_pointer_region_nest package)) as [|bound [|second rest]] eqn:BOUNDS;
    [exact None| |exact None].
  destruct (memory_nest_iterators (multi_pointer_region_nest package)) as [|iterator [|other tail]] eqn:ITERS;
    [exact None| |exact None].
  exact (Some (@MemoryAffinePointerPackage source package bound iterator BOUNDS ITERS)).
Defined.
Definition describe_memory_affine_pointer_region source :=
  let nest := propose_memory_source_nest (progress_syntax_size source) source in
  let extent := 1024 in
  let scalars := propose_memory_pointer_scalars (memory_nest_iterators nest) (flatten_region (memory_nest_leaf nest)) in
  match propose_memory_scalar_pointer_computes extent (memory_nest_iterators nest) scalars (flatten_region (memory_nest_leaf nest)) with
  | Some (operation::operations) =>
      match check_memory_multi_pointer_region_with_resource false source nest
        (Z.min extent (propose_memory_triple_cap (operation::operations)))
        (memory_multi_pointer_operation_identifiers (operation::operations)) extent scalars (operation::operations) with
      | Some package => check_memory_affine_pointer_package package | None => None end
  | _ => None end.
Definition memory_affine_pointer_access_cell access index :=
  point_cell (memory_nary_access_array access) (memory_nary_index_value (memory_nary_access_index access) [index]).
Lemma memory_affine_pointer_point_footprint extra operations index :
  memory_point_footprint (memory_pad_instructions extra (map memory_nary_compute_instruction operations)) [index] =
    map (fun access => memory_affine_pointer_access_cell access index) (memory_linear_pointer_accesses operations).
Proof.
  induction operations as [|operation operations IH]; [reflexivity|].
  cbn [memory_point_footprint memory_pad_instructions map flat_map].
  rewrite memory_pad_instruction_footprint.
  change (memory_instruction_footprint (memory_nary_compute_instruction operation) [index] ++
    memory_point_footprint (memory_pad_instructions extra (map memory_nary_compute_instruction operations)) [index] =
      map (fun access => memory_affine_pointer_access_cell access index) (memory_linear_pointer_accesses (operation::operations))).
  rewrite IH; unfold memory_linear_pointer_accesses; cbn [flat_map]; rewrite map_app; f_equal.
  unfold memory_instruction_footprint; cbn [memory_nary_compute_instruction instruction_write instruction_reads].
  rewrite map_map; reflexivity.
Qed.
Theorem memory_affine_pointer_runtime_footprint source (package : memory_affine_pointer_package source) temps count :
  temps ! (affine_pointer_bound package) = Some (Vint (Int.repr count)) -> signed_range count ->
  memory_multi_pointer_runtime_footprint (affine_pointer_region package) temps =
    flat_map (fun index => map (fun access => memory_affine_pointer_access_cell access index)
      (memory_linear_pointer_accesses (multi_pointer_region_code (affine_pointer_region package)))) (Zrange 0 count).
Proof.
  intros BOUND RANGE.
  assert (DIMENSIONS : length (memory_nest_iterators (multi_pointer_region_nest (affine_pointer_region package))) = 1%nat).
  { rewrite (affine_pointer_one_iterator package); reflexivity. }
  pose proof (@memory_multi_pointer_source_footprint source (affine_pointer_region package) [count]
    (memory_recursive_parameters (multi_pointer_region_scalars (affine_pointer_region package)) temps)
    ltac:(cbn; symmetry; exact DIMENSIONS)) as FOOTPRINT.
  unfold memory_recursive_parameters,temp_word in FOOTPRINT.
  rewrite length_map in FOOTPRINT; cbn [length app] in FOOTPRINT.
  unfold memory_multi_pointer_runtime_footprint,memory_multi_pointer_runtime_context,memory_multi_pointer_runtime_loop.
  rewrite DIMENSIONS; unfold memory_recursive_parameters; rewrite map_app,(affine_pointer_one_bound package).
  cbn [map]; unfold temp_word; rewrite BOUND,Int.signed_repr by exact RANGE.
  cbn [app]; rewrite FOOTPRINT.
  cbn [memory_rectangular_points app].
  rewrite memory_flat_map_associative; apply memory_flat_map_ext_in; intros index MEMBER.
  cbn [flat_map app]; rewrite app_nil_r.
  unfold memory_multi_pointer_region_instructions; apply memory_affine_pointer_point_footprint.

Qed.

Theorem memory_affine_pointer_footprint_member source (package : memory_affine_pointer_package source) temps count cell :
  temps ! (affine_pointer_bound package) = Some (Vint (Int.repr count)) -> signed_range count ->
  (In cell (memory_multi_pointer_runtime_footprint (affine_pointer_region package) temps) <->
    exists access index,
      In access (memory_linear_pointer_accesses (multi_pointer_region_code (affine_pointer_region package))) /\
      0 <= index < count /\ cell = memory_affine_pointer_access_cell access index).
Proof.
  intros BOUND RANGE; rewrite (@memory_affine_pointer_runtime_footprint source package temps count BOUND RANGE).
  rewrite in_flat_map; split.
  - intros [index [INDEX CELL]]; apply Zrange_in in INDEX; apply in_map_iff in CELL as [access [SAME MEMBER]].
    exists access,index; auto.
  - intros [access [index [MEMBER [INDEX ->]]]]; exists index; split;
      [apply Zrange_in; exact INDEX|apply in_map_iff; exists access; auto].
Qed.


Lemma memory_affine_pointer_accesses_valid source (package : memory_affine_pointer_package source) :
  Forall (memory_multi_pointer_access_valid
    (memory_recursive_limits (multi_pointer_region_nest (affine_pointer_region package)) (multi_pointer_region_limit (affine_pointer_region package)))
    [affine_pointer_iterator package] (multi_pointer_region_window (affine_pointer_region package)))
    (memory_linear_pointer_accesses (multi_pointer_region_code (affine_pointer_region package))).
Proof.
  pose proof (multi_pointer_region_operations (multi_pointer_region_syntax (affine_pointer_region package))) as OPS.
  rewrite (affine_pointer_one_iterator package) in OPS.
  induction OPS as [|operation operations [WRITE [READS VALUE]] REST IH]; cbn [memory_linear_pointer_accesses flat_map].
  - constructor.
  - apply Forall_app; split; [constructor; assumption|exact IH].
Qed.
Lemma memory_affine_pointer_accesses_encoding source (package : memory_affine_pointer_package source) access :
  In access (memory_linear_pointer_accesses (multi_pointer_region_code (affine_pointer_region package))) ->
  memory_encode_nary_index [affine_pointer_iterator package] (memory_nary_access_expression access) = Some (memory_nary_access_index access).
Proof.
  intro MEMBER; pose proof (memory_affine_pointer_accesses_valid package) as VALID.
  apply Forall_forall with (x := access) in VALID; [|exact MEMBER].
  exact (proj1 (proj2 (proj1 VALID))).
Qed.
Lemma memory_affine_pointer_accesses_covered source (package : memory_affine_pointer_package source) :
  Forall (fun access => In (memory_nary_access_array access) (multi_pointer_region_pointers (affine_pointer_region package)))
    (memory_linear_pointer_accesses (multi_pointer_region_code (affine_pointer_region package))).
Proof.
  pose proof (multi_pointer_region_covered (multi_pointer_region_syntax (affine_pointer_region package))) as OPS.
  induction OPS as [|operation operations [WRITE READS] REST IH]; cbn [memory_linear_pointer_accesses flat_map].
  - constructor.
  - apply Forall_app; split; [constructor; assumption|exact IH].
Qed.
Print Assumptions check_memory_affine_pointer_package.
Print Assumptions memory_affine_pointer_runtime_footprint.
Print Assumptions memory_affine_pointer_accesses_encoding.
