From Stdlib Require Import List Bool.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax GuardMemoryAffineInnerPointerRegionSource.
From GuardInterface Require Import ClightAffineSnapshotSyntax ClightAffineSnapshotRows
  ClightAffineSnapshotRowObservation ClightZeroRmwObservation.
Set Implicit Arguments.

(** Choose ordinary source data, then check its complete row code. No
    semantic predicate or completion proof comes from the source proposer. *)
Fixpoint find_affine_snapshot_rmw_alpha code identifiers : option ident :=
  match identifiers with
  | nil => None
  | alpha::rest => if check_zero_rmw_control alpha code then Some alpha
      else find_affine_snapshot_rmw_alpha code rest
  end.

Lemma find_affine_snapshot_rmw_alpha_sound code identifiers alpha :
  find_affine_snapshot_rmw_alpha code identifiers=Some alpha ->
  In alpha identifiers /\ check_zero_rmw_control alpha code=true.
Proof.
  induction identifiers as [|head rest IH]; cbn; [discriminate|].
  destruct(check_zero_rmw_control head code)eqn:CHECK.
  - intro FOUND; injection FOUND as <-; split; [left; reflexivity|exact CHECK].
  - intro FOUND; destruct(IH FOUND)as [MEMBER CHECKED]; split; [right; exact MEMBER|exact CHECKED].
Qed.

Definition check_affine_snapshot_rmw_site original(site:affine_snapshot_source_package original) :
  option(affine_snapshot_rmw_site site).
Proof.
  destruct(find_affine_snapshot_rmw_alpha
    (affine_snapshot_body(snapshot_cached_package site)(snapshot_original_header site))
    (memory_affine_inner_pointer_region_context(snapshot_cached_package site)))as [alpha|]eqn:FOUND.
  - destruct(@find_affine_snapshot_rmw_alpha_sound
      (affine_snapshot_body(snapshot_cached_package site)(snapshot_original_header site))
      (memory_affine_inner_pointer_region_context(snapshot_cached_package site))alpha FOUND)
      as [MEMBER CHECKED].
    exact(Some(@Build_affine_snapshot_rmw_site original site alpha MEMBER CHECKED)).
  - exact None.
Defined.

Print Assumptions find_affine_snapshot_rmw_alpha_sound.
Print Assumptions check_affine_snapshot_rmw_site.
