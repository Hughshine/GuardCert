From Stdlib Require Import List Bool ZArith.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightStructuredProgress ClightStraightLine ClightPrivateRegion.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryNaryCompute
  GuardMemoryNaryAffineAccess GuardMemoryMultiPointerSyntax GuardMemoryMultiPointerIdentifiers
  GuardMemoryScalarPointerComputeSyntax GuardMemoryRecursiveSource GuardMemoryRecursiveSyntax
  GuardMemoryTripleSyntax.
Import CoreAlarmed ListNotations PrivateRegion.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition describe_memory_axis_pointer_region_at requested_cap source :=
  let nest := propose_memory_source_nest (progress_syntax_size source) source in
  if Nat.leb 2 (length (memory_nest_iterators nest)) then
    let extent := 1024 in
    let scalars := propose_memory_pointer_scalars (memory_nest_iterators nest) (flatten_region (memory_nest_leaf nest)) in
    match propose_memory_scalar_pointer_computes extent (memory_nest_iterators nest) scalars
      (flatten_region (memory_nest_leaf nest)) with
    | Some (operation::operations) =>
        check_memory_multi_pointer_region_with_resource false source nest
          (Z.min requested_cap (Z.min extent (propose_memory_triple_cap (operation::operations))))
          (memory_multi_pointer_operation_identifiers (operation::operations)) extent scalars (operation::operations)
    | _ => None end
  else None.

Fixpoint check_memory_axis_pointer_caps source
  (check : memory_multi_pointer_region_package source -> CoreAlarmed.Base.imp (option statement)) caps :=
  match caps with
  | [] => pure None
  | cap::rest => match describe_memory_axis_pointer_region_at cap source with
      | Some package => BIND candidate <- check package -;
          match candidate with Some target => pure (Some target) | None => check_memory_axis_pointer_caps check rest end
      | None => check_memory_axis_pointer_caps check rest end
  end.

Theorem check_memory_axis_pointer_caps_sound source live
  (check : memory_multi_pointer_region_package source -> CoreAlarmed.Base.imp (option statement)) :
  (forall package target, mayReturn (check package) (Some target) -> projected_region_contract live source target) ->
  forall caps target,
    mayReturn (check_memory_axis_pointer_caps check caps) (Some target) -> projected_region_contract live source target.
Proof.
  intros CHECK caps; induction caps as [|cap caps IH]; intros target RUN; cbn [check_memory_axis_pointer_caps] in RUN.
  - apply mayReturn_pure in RUN; discriminate.
  - destruct (describe_memory_axis_pointer_region_at cap source) as [package|].
    + bind_imp_destruct RUN candidate ACCEPTED; destruct candidate as [candidate|].
      * apply mayReturn_pure in RUN; inversion RUN; subst target; apply CHECK with (package := package); exact ACCEPTED.
      * apply IH; exact RUN.
    + apply IH; exact RUN.
Qed.

Definition memory_axis_pointer_search_caps : list Z := [1024;64;32;16;8;4;1].
