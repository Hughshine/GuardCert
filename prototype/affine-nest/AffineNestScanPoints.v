From Stdlib Require Import List ZArith.
From compcert.common Require Import AST.
From polcert.lib Require Import Misc.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation.
From GuardAffineNest Require Import AffineNestSyntax AffineNestScanModel.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** This finite list is a proof witness. The generated guard uses bounded
    loops and never materializes the source point list at runtime. *)
Fixpoint affine_scan_points nest valuation lower : list(ident->Z) := match nest with
  | AffineSourceLeaf _=>[valuation]
  | AffineSourceAxis iterator _ expression _ child=>flat_map
      (fun value=>affine_scan_points child(memory_source_set_valuation valuation iterator value) 0)
      (Zrange lower(memory_source_affine_math valuation expression)) end.

Lemma affine_scan_points_exact nest : forall valuation lower point,
  In point(affine_scan_points nest valuation lower) <-> affine_scan_point nest valuation lower point.
Proof.
  induction nest as [source|iterator bound expression body child IH]; intros valuation lower point; cbn [affine_scan_points].
  - split; [intros [<-|[]]; constructor|intro POINT; inversion POINT; subst; cbn; auto].
  - rewrite in_flat_map; split.
    + intros [value [RANGE MEMBER]]; econstructor; [|apply IH; exact MEMBER].
      apply Zrange_in in RANGE; exact RANGE.
    + intro POINT; inversion POINT; subst; eexists; split; [apply Zrange_in; eassumption|apply IH; eassumption].
Qed.
Print Assumptions affine_scan_points_exact.
