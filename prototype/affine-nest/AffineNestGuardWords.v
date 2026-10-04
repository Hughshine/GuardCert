From Stdlib Require Import List.
From compcert.lib Require Import Maps Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestSourceDecode
  AffineNestFirstDomain AffineNestFirstLeaf AffineNestBoundWords AffineNestLeafModel AffineNestUsedWords.
Import ListNotations.
Set Implicit Arguments.

Definition affine_guard_register_used nest layout scalars operations identifier := match nest with
  | AffineSourceLeaf _ => affine_leaf_register_used layout scalars operations identifier
  | AffineSourceAxis _ bound _ _ _ => identifier=bound \/
      In identifier(affine_tail_bound_reads nest) \/ affine_leaf_register_used layout scalars operations identifier end.

Theorem affine_source_guard_register_defined nest bounds lower upper layout scalars pointers operations
  (certificate:affine_leaf_certificate (affine_nest_leaf nest) bounds lower upper layout scalars pointers operations)
  fe ge locals temps memory after final identifier :
  affine_nest_shapes nest -> NoDup(affine_nest_controls nest) ->
  ~In identifier(affine_nest_mutated nest) -> affine_first_path_active nest temps ->
  affine_guard_register_used nest layout scalars operations identifier ->
  exec_stmt fe ge locals temps memory (affine_nest_source nest) E0 after final Out_normal ->
  exists word,temps!identifier=Some(Vint word).
Proof.
  intros SHAPES FRESH PROTECTED ACTIVE USED SOURCE.
  destruct nest as [leaf|iterator bound expression body child].
  - eapply affine_leaf_actual_used_word; eassumption.
  - pose proof(@affine_source_first_header_domain (AffineSourceAxis iterator bound expression body child)
      fe ge locals temps memory after final SHAPES FRESH (affine_leaf_normal certificate)
      (affine_leaf_quiet certificate) (affine_leaf_writes certificate) SOURCE) as HEADERS.
    destruct(peq identifier bound) as [->|NOT_BOUND].
    + destruct HEADERS as [_ [WORD _]]; exact WORD.
    + destruct USED as [SAME|[BOUND_USED|LEAF_USED]]; [contradiction| |].
      * eapply affine_first_headers_used_bound_word; eassumption.
      * eapply affine_source_used_leaf_word; try eassumption.
        intro MEMBER; apply PROTECTED;
          cbn [affine_nest_mutated affine_nest_controls List.In] in *; intuition congruence.
Qed.
Print Assumptions affine_source_guard_register_defined.
