From Stdlib Require Import List.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightTempFrame.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightPrivateScan ClightSourceObservation.
Import ListNotations.
Set Implicit Arguments.

(** Retain the value of a real source preload as well as its capability. The
    outputs of the remaining prefix may not overwrite this value or pointer.
    No assertion about subsequent body stores is part of the receipt. *)
Theorem source_preload_value target pointer rest fe ge locals temps memory trace after final outcome :
  pointer <> target -> ~ In target (source_load_targets rest) -> ~ In pointer (source_load_targets rest) ->
  exec_stmt fe ge locals temps memory (source_load_prefix ((target,pointer)::rest)) trace after final outcome ->
  exists block offset value,
    after ! target = Some value /\ after ! pointer = Some (Vptr block offset) /\
    Mem.loadv Mint32 final (Vptr block offset) = Some value.
Proof.
  intros DISTINCT TARGET_FRESH POINTER_FRESH RUN; cbn [source_load_prefix] in RUN; inversion RUN; subst.
  2: match goal with SET : exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ |- _ => inversion SET; subst; contradiction end.
  match goal with SET : exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ |- _ => inversion SET; subst end.
  match goal with LOAD : eval_expr _ _ _ _ (signed_load _) _ |- _ =>
    apply signed_load_inv in LOAD as [block [offset [POINTER READ]]] end.
  match goal with TAIL : exec_stmt _ _ _ _ _ (source_load_prefix rest) _ _ _ _ |- _ =>
    pose proof TAIL as TAIL_RUN;
    destruct (@private_scan_completed_shape _ _ _ _ _ _ _ _ _ _ TAIL
      (source_load_prefix_supported rest)) as [_ [MEMORY _]]; subst end.
  exists block,offset; eexists; split.
  - rewrite (writes_only_frame TAIL_RUN (source_load_prefix_writes rest) target TARGET_FRESH); apply PTree.gss.
  - split; [|exact READ].
    rewrite (writes_only_frame TAIL_RUN (source_load_prefix_writes rest) pointer POINTER_FRESH), PTree.gso
      by exact DISTINCT; exact POINTER.
Qed.

Print Assumptions source_preload_value.
