From Stdlib Require Import List.
From compcert.lib Require Import Maps.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightFiniteRegion ClightStraightLine ClightTempFrame.
From GuardMemory Require Import GuardMemoryNaryCompute GuardMemoryPointerCompute
  GuardMemorySourceParameters GuardMemoryParamPointerSyntax GuardMemoryWindowSequence
  GuardMemoryWindowWords GuardMemoryPointerSourceWords.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestFirstLeaf AffineNestLeafModel.
Import ListNotations.
Set Implicit Arguments.

Definition affine_leaf_register_used layout scalars operations identifier :=
  exists operation, In operation operations /\
    (In identifier (memory_pointer_operation_address_reads operation) \/
     exists index, nth_error (layout++scalars) index=Some identifier /\
       In index (memory_source_parameter_positions (memory_nary_compute_value operation))).

Theorem affine_leaf_actual_used_word source bounds lower upper layout scalars pointers operations
  (certificate:affine_leaf_certificate source bounds lower upper layout scalars pointers operations)
  fe ge locals temps memory after final identifier :
  affine_leaf_register_used layout scalars operations identifier ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  exists word, temps!identifier=Some(Vint word).
Proof.
  intros [operation [MEMBER [ADDRESS|[index [LOOKUP USED]]]]] SOURCE;
    apply flatten_region_execution in SOURCE; rewrite (affine_leaf_exact certificate) in SOURCE.
  - eapply window_sequence_address_words; [exact(affine_leaf_valid certificate)|exact SOURCE|exact MEMBER|exact ADDRESS].
  - eapply window_sequence_used_register; [exact(affine_leaf_valid certificate)|exact LOOKUP|exact SOURCE|exact MEMBER|exact USED].
Qed.

Theorem affine_source_used_leaf_word nest bounds lower upper layout scalars pointers operations
  (certificate:affine_leaf_certificate (affine_nest_leaf nest) bounds lower upper layout scalars pointers operations)
  fe ge locals temps memory after final identifier :
  affine_nest_shapes nest -> NoDup(affine_nest_controls nest) ->
  ~In identifier (affine_nest_controls nest) ->
  affine_first_path_active nest temps ->
  affine_leaf_register_used layout scalars operations identifier ->
  exec_stmt fe ge locals temps memory (affine_nest_source nest) E0 after final Out_normal ->
  exists word, temps!identifier=Some(Vint word).
Proof.
  intros SHAPES FRESH PROTECTED ACTIVE USED SOURCE.
  assert (PRIVATE:forall key, In key [identifier] -> ~In key (affine_nest_controls nest)).
  { intros key MEMBER; cbn in MEMBER; destruct MEMBER as [SAME|BAD]; [subst; exact PROTECTED|contradiction]. }
  destruct (@affine_source_first_leaf nest fe ge locals [identifier] temps memory after final
    SHAPES FRESH (affine_leaf_normal certificate) (affine_leaf_quiet certificate)
    (affine_leaf_writes certificate) PRIVATE ACTIVE SOURCE)
    as [leaf_temps [leaf_after [leaf_final [FRAME LEAF]]]].
  destruct (@affine_leaf_actual_used_word _ _ _ _ _ _ _ _ certificate fe ge locals leaf_temps memory
    leaf_after leaf_final identifier USED LEAF) as [word WORD].
  exists word; rewrite (FRAME identifier (or_introl eq_refl)) in WORD; exact WORD.
Qed.
Print Assumptions affine_leaf_actual_used_word.
Print Assumptions affine_source_used_leaf_word.
