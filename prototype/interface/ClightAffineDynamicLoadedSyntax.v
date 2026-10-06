From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightSyntaxEquality ClightFrontendLoopProtocol.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax GuardMemoryAffinePointerLoadedDomain
  GuardMemoryMultiPointerIdentifiers GuardMemoryRecursiveSyntax.
From GuardInterface Require Import ClightLoadedSequenceProgress ClightObservedPointerSyntax
  ClightSourceObservation ClightAffineInnerPointerCandidates ClightAffineLoadedSourceSyntax.
Import ListNotations.
Set Implicit Arguments.

Record affine_dynamic_loaded_body_package source := AffineDynamicLoadedBodyPackage {
  dynamic_loaded_body_cached_source : statement;
  dynamic_loaded_body_cached_package : memory_affine_inner_pointer_package dynamic_loaded_body_cached_source;
  dynamic_loaded_body_pointer : ident;
  dynamic_loaded_body_exact : source = memory_affine_pointer_loaded_source dynamic_loaded_body_cached_package dynamic_loaded_body_pointer;
  dynamic_loaded_body_pointer_fresh :
    dynamic_loaded_body_pointer <> affine_inner_pointer_row (affine_inner_pointer_shape dynamic_loaded_body_cached_package) /\
    dynamic_loaded_body_pointer <> affine_inner_pointer_column (affine_inner_pointer_shape dynamic_loaded_body_cached_package) /\
    dynamic_loaded_body_pointer <> affine_inner_pointer_inner_bound (affine_inner_pointer_shape dynamic_loaded_body_cached_package)
}.

Definition check_affine_dynamic_loaded_body source cached_source
  (package : memory_affine_inner_pointer_package cached_source) (pointer : ident) :
  option (affine_dynamic_loaded_body_package source).
Proof.
  destruct (statement_eq source (memory_affine_pointer_loaded_source package pointer)) as [SOURCE|]; [|exact None].
  destruct (peq pointer (affine_inner_pointer_row (affine_inner_pointer_shape package))) as [|ROW]; [exact None|].
  destruct (peq pointer (affine_inner_pointer_column (affine_inner_pointer_shape package))) as [|COLUMN]; [exact None|].
  destruct (peq pointer (affine_inner_pointer_inner_bound (affine_inner_pointer_shape package))) as [|INNER]; [exact None|].
  exact (Some (@AffineDynamicLoadedBodyPackage source cached_source package pointer SOURCE (conj ROW (conj COLUMN INNER)))).
Defined.

Record affine_dynamic_loaded_region_package source := AffineDynamicLoadedRegionPackage {
  dynamic_loaded_region_observed : observed_pointer_source_package source;
  dynamic_loaded_region_body : affine_dynamic_loaded_body_package (observed_source_loop dynamic_loaded_region_observed);
  dynamic_loaded_region_outputs_unique : NoDup (source_load_targets (observed_source_loads dynamic_loaded_region_observed));
  dynamic_loaded_region_observations : source_observations_check
    (affine_inner_pointer_pointers (dynamic_loaded_body_cached_package dynamic_loaded_region_body))
    (observed_source_loads dynamic_loaded_region_observed) = true;
  dynamic_loaded_region_snapshot_receipt : In
    (affine_inner_pointer_bound (affine_inner_pointer_shape (dynamic_loaded_body_cached_package dynamic_loaded_region_body)),
      dynamic_loaded_body_pointer dynamic_loaded_region_body)
    (observed_source_loads dynamic_loaded_region_observed)
}.

Definition check_affine_dynamic_loaded_region source (observed : observed_pointer_source_package source)
  (body : affine_dynamic_loaded_body_package (observed_source_loop observed)) :
  option (affine_dynamic_loaded_region_package source).
Proof.
  destruct (memory_identifiers_unique_check (source_load_targets (observed_source_loads observed))) eqn:UNIQUE; [|exact None].
  destruct (source_observations_check (affine_inner_pointer_pointers (dynamic_loaded_body_cached_package body))
    (observed_source_loads observed)) eqn:OBSERVED; [|exact None].
  destruct (source_snapshot_receipt_check
    (affine_inner_pointer_bound (affine_inner_pointer_shape (dynamic_loaded_body_cached_package body)))
    (dynamic_loaded_body_pointer body) (observed_source_loads observed)) eqn:RECEIPT; [|exact None].
  exact (Some (@AffineDynamicLoadedRegionPackage source observed body
    (@memory_identifiers_unique_check_sound _ UNIQUE) OBSERVED (@source_snapshot_receipt_check_sound _ _ _ RECEIPT))).
Defined.

(** The same untrusted source metadata interface is reused. An independent
    bound pointer needs loop-control freshness and a retained source receipt;
    its physical separation is established by the generated runtime guard. *)
Definition describe_affine_dynamic_loaded_source (profile : affine_inner_pointer_profiler) source :=
  match describe_observed_pointer_source source with
  | Some observed =>
    match checked_loaded_progress (observed_source_loop observed) with
    | Some (row,pointer,outer) =>
      match find (fun load => Pos.eqb (snd load) pointer) (observed_source_loads observed) with
      | Some (cache,_) =>
        let cached_source := frontend_counted_loop row cache outer in
        match profile cached_source with
        | Some metadata => match describe_affine_inner_pointer_at cached_source metadata with
          | Some package => match check_affine_dynamic_loaded_body (observed_source_loop observed) package pointer with
            | Some body => check_affine_dynamic_loaded_region observed body
            | None => None end
          | None => None end
        | None => None end
      | None => None end
    | None => None end
  | None => None end.

Print Assumptions check_affine_dynamic_loaded_body.
Print Assumptions check_affine_dynamic_loaded_region.
Print Assumptions describe_affine_dynamic_loaded_source.
