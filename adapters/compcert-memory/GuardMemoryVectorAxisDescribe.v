From Stdlib Require Import List Bool ZArith.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightStructuredProgress ClightStraightLine ClightPrivateRegion.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryNaryCompute
  GuardMemoryNaryAffineAccess GuardMemoryMultiPointerIdentifiers GuardMemoryMultiPointerCompute GuardMemoryMultiPointerComputeSyntax
  GuardMemoryScalarPointerComputeSyntax GuardMemoryRecursiveSource GuardMemoryRecursiveSyntax.
From GuardMemory Require Import GuardMemoryVectorPointerSyntax.
From GuardMemory Require Import GuardMemoryMultiPointerComputeSyntax.
Import CoreAlarmed ListNotations PrivateRegion.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint memory_vector_replace_axis (axis : nat) (value : Z) (caps : list Z) :=
  match axis,caps with
  | O,_::rest => value::rest
  | S slot,cap::rest => cap::memory_vector_replace_axis slot value rest
  | _,[] => [] end.
Fixpoint memory_vector_grow_axis fuel (valid : list Z -> bool) axis caps lower upper :=
  match fuel with
  | O => caps
  | S rest => if lower <=? upper then
      let middle := (lower+upper)/2 in
      let proposed := memory_vector_replace_axis axis middle caps in
      if valid proposed then memory_vector_grow_axis rest valid axis proposed (middle+1) upper
      else memory_vector_grow_axis rest valid axis caps lower (middle-1)
    else caps end.
Fixpoint memory_vector_grow_axes fuel (valid : list Z -> bool) axis caps :=
  match fuel with
  | O => caps
  | S rest => memory_vector_grow_axes rest valid (S axis)
      (memory_vector_grow_axis 12 valid axis caps 1 1024) end.
Definition memory_vector_propose_caps nest scalars operations :=
  let dimensions := length (memory_nest_iterators nest) in
  let valid := fun caps => forallb (memory_multi_pointer_compute_check caps (memory_nest_iterators nest) scalars 1024) operations in
  memory_vector_grow_axes dimensions valid O (repeat 1 dimensions).
Definition memory_vector_cap_profiles caps :=
  caps :: flat_map (fun axis => map (fun upper =>
    memory_vector_replace_axis axis (Z.min upper (nth axis caps 1)) caps) [8;4;1]) (seq O (length caps)) ++
  [repeat 1 (length caps)].
Definition describe_memory_vector_axis_at source caps :=
  let nest := propose_memory_source_nest (progress_syntax_size source) source in
  if Nat.leb 2 (length (memory_nest_iterators nest)) then
    let scalars := propose_memory_pointer_scalars (memory_nest_iterators nest) (flatten_region (memory_nest_leaf nest)) in
    match propose_memory_scalar_pointer_computes 1024 (memory_nest_iterators nest) scalars (flatten_region (memory_nest_leaf nest)) with
    | Some (operation::operations) => check_memory_vector_pointer_region source nest caps
        (memory_multi_pointer_operation_identifiers (operation::operations)) 1024 scalars (operation::operations)
    | _ => None end
  else None.
Definition propose_memory_vector_axis_profiles source :=
  let nest := propose_memory_source_nest (progress_syntax_size source) source in
  let scalars := propose_memory_pointer_scalars (memory_nest_iterators nest) (flatten_region (memory_nest_leaf nest)) in
  match propose_memory_scalar_pointer_computes 1024 (memory_nest_iterators nest) scalars (flatten_region (memory_nest_leaf nest)) with
  | Some operations => memory_vector_cap_profiles (memory_vector_propose_caps nest scalars operations)
  | None => [] end.
Fixpoint check_memory_vector_axis_profiles source
  (check : memory_vector_pointer_region_package source -> CoreAlarmed.Base.imp (option statement)) profiles :=
  match profiles with
  | [] => pure None
  | caps::rest => match describe_memory_vector_axis_at source caps with
    | Some package => BIND candidate <- check package -;
        match candidate with Some target => pure (Some target) | None => check_memory_vector_axis_profiles check rest end
    | None => check_memory_vector_axis_profiles check rest end end.
Theorem check_memory_vector_axis_profiles_sound source live
  (check : memory_vector_pointer_region_package source -> CoreAlarmed.Base.imp (option statement)) :
  (forall package target, mayReturn (check package) (Some target) -> projected_region_contract live source target) ->
  forall profiles target, mayReturn (check_memory_vector_axis_profiles check profiles) (Some target) ->
    projected_region_contract live source target.
Proof.
  intros CHECK profiles; induction profiles as [|caps profiles IH]; intros target RUN; cbn [check_memory_vector_axis_profiles] in RUN.
  - apply mayReturn_pure in RUN; discriminate.
  - destruct (describe_memory_vector_axis_at source caps) as [package|].
    + bind_imp_destruct RUN candidate ACCEPTED; destruct candidate as [candidate|].
      * apply mayReturn_pure in RUN; inversion RUN; subst target; apply CHECK with (package := package); exact ACCEPTED.
      * apply IH; exact RUN.
    + apply IH; exact RUN.
Qed.
Print Assumptions check_memory_vector_axis_profiles_sound.
