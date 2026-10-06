From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightSyntaxEquality ClightFrontendLoopProtocol.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax GuardMemoryAffinePointerLoadedDomain
  GuardMemoryObservationExclusion GuardMemoryMultiPointerIdentifiers GuardMemoryRecursiveSyntax.
From GuardInterface Require Import ClightLoadedSequenceProgress ClightObservedPointerSyntax
  ClightSourceObservation ClightAffineInnerPointerCandidates.
Import ListNotations.
Set Implicit Arguments.

Record affine_loaded_body_package source := AffineLoadedBodyPackage {
  loaded_body_cached_source : statement;
  loaded_body_cached_package : memory_affine_inner_pointer_package loaded_body_cached_source;
  loaded_body_pointer : ident;
  loaded_body_exact : source = memory_affine_pointer_loaded_source loaded_body_cached_package loaded_body_pointer;
  loaded_body_pointer_member : In loaded_body_pointer (affine_inner_pointer_pointers loaded_body_cached_package);
  loaded_body_observation_excluded : memory_writes_exclude_cell
    (memory_affine_inner_pointer_limits (affine_inner_pointer_row_limit loaded_body_cached_package)
      (affine_inner_pointer_column_limit loaded_body_cached_package)
      (affine_inner_pointer_header_limits loaded_body_cached_package)
      (affine_inner_pointer_body_limits loaded_body_cached_package))
    (affine_inner_pointer_extent loaded_body_cached_package) loaded_body_pointer 0%Z
    (affine_inner_pointer_operations loaded_body_cached_package) = true
}.

Definition check_affine_loaded_body source cached_source
  (package : memory_affine_inner_pointer_package cached_source) (pointer : ident) : option (affine_loaded_body_package source).
Proof.
  destruct (statement_eq source (memory_affine_pointer_loaded_source package pointer)) as [SOURCE|]; [|exact None].
  destruct (in_dec peq pointer (affine_inner_pointer_pointers package)) as [MEMBER|]; [|exact None].
  destruct (memory_writes_exclude_cell
    (memory_affine_inner_pointer_limits (affine_inner_pointer_row_limit package) (affine_inner_pointer_column_limit package)
      (affine_inner_pointer_header_limits package) (affine_inner_pointer_body_limits package))
    (affine_inner_pointer_extent package) pointer 0%Z (affine_inner_pointer_operations package)) eqn:EXCLUDED; [|exact None].
  exact (Some (@AffineLoadedBodyPackage source cached_source package pointer SOURCE MEMBER EXCLUDED)).
Defined.

Definition source_snapshot_receipt_check cache pointer loads :=
  existsb (fun load => Pos.eqb (fst load) cache && Pos.eqb (snd load) pointer) loads.
Lemma source_snapshot_receipt_check_sound cache pointer loads :
  source_snapshot_receipt_check cache pointer loads = true -> In (cache,pointer) loads.
Proof.
  unfold source_snapshot_receipt_check; rewrite existsb_exists.
  intros [[target address] [MEMBER SAME]]; cbn in SAME;
    rewrite andb_true_iff,!Pos.eqb_eq in SAME; destruct SAME; subst; exact MEMBER.
Qed.

Record affine_loaded_region_package source := AffineLoadedRegionPackage {
  loaded_region_observed : observed_pointer_source_package source;
  loaded_region_body : affine_loaded_body_package (observed_source_loop loaded_region_observed);
  loaded_region_outputs_unique : NoDup (source_load_targets (observed_source_loads loaded_region_observed));
  loaded_region_observations : source_observations_check
    (affine_inner_pointer_pointers (loaded_body_cached_package loaded_region_body))
    (observed_source_loads loaded_region_observed) = true;
  loaded_region_snapshot_receipt : In
    (affine_inner_pointer_bound (affine_inner_pointer_shape (loaded_body_cached_package loaded_region_body)),
      loaded_body_pointer loaded_region_body)
    (observed_source_loads loaded_region_observed)
}.

Definition check_affine_loaded_region source (observed : observed_pointer_source_package source)
  (body : affine_loaded_body_package (observed_source_loop observed)) : option (affine_loaded_region_package source).
Proof.
  destruct (memory_identifiers_unique_check (source_load_targets (observed_source_loads observed))) eqn:UNIQUE; [|exact None].
  destruct (source_observations_check (affine_inner_pointer_pointers (loaded_body_cached_package body))
    (observed_source_loads observed)) eqn:OBSERVED; [|exact None].
  destruct (source_snapshot_receipt_check
    (affine_inner_pointer_bound (affine_inner_pointer_shape (loaded_body_cached_package body)))
    (loaded_body_pointer body) (observed_source_loads observed)) eqn:RECEIPT; [|exact None].
  exact (Some (@AffineLoadedRegionPackage source observed body
    (@memory_identifiers_unique_check_sound _ UNIQUE) OBSERVED (@source_snapshot_receipt_check_sound _ _ _ RECEIPT))).
Defined.

(** Source and metadata proposal are untrusted. The returned record binds the
    actual loaded loop, a checked cached model, safe source receipts and static
    write exclusion. No temporary identifier is fixed by this selector. *)
Definition describe_affine_loaded_source (profile : affine_inner_pointer_profiler) source :=
  match describe_observed_pointer_source source with
  | Some observed =>
    match checked_loaded_progress (observed_source_loop observed) with
    | Some (row,pointer,outer) =>
      match find (fun load => Pos.eqb (snd load) pointer) (observed_source_loads observed) with
      | Some (cache,_) =>
        let cached_source := frontend_counted_loop row cache outer in
        match profile cached_source with
        | Some metadata => match describe_affine_inner_pointer_at cached_source metadata with
          | Some package => match check_affine_loaded_body (observed_source_loop observed) package pointer with
            | Some body => check_affine_loaded_region observed body
            | None => None end
          | None => None end
        | None => None end
      | None => None end
    | None => None end
  | None => None end.

Print Assumptions check_affine_loaded_body.
Print Assumptions source_snapshot_receipt_check_sound.
Print Assumptions check_affine_loaded_region.
Print Assumptions describe_affine_loaded_source.
