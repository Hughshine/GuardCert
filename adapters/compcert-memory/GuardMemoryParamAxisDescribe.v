From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight Cop.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightStructuredProgress ClightStraightLine ClightPrivateRegion.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryNaryCompute
  GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceReifier GuardMemoryNaryAffineAccess
  GuardMemoryMultiPointerIdentifiers GuardMemoryMultiPointerCompute GuardMemoryMultiPointerComputeSyntax
  GuardMemoryScalarPointerComputeSyntax GuardMemoryRecursiveSource GuardMemoryRecursiveSyntax GuardMemoryVectorAxisDescribe.
From GuardMemory Require Import GuardMemoryParamPointerSyntax.
Import CoreAlarmed ListNotations PrivateRegion.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint memory_pointer_expression_address_registers source : list ident :=
  match source with
  | Ederef (Ebinop Oadd (Etempvar _ _) index _) _ =>
      match propose_memory_source_affine index with Some expression => memory_source_affine_reads expression | None => [] end
  | Ebinop _ first second _ => memory_pointer_expression_address_registers first++memory_pointer_expression_address_registers second
  | Eunop _ inner _ | Ecast inner _ => memory_pointer_expression_address_registers inner
  | _ => [] end.
Definition memory_pointer_statement_address_registers source :=
  match source with Sassign lhs rhs => memory_pointer_expression_address_registers lhs++memory_pointer_expression_address_registers rhs | _ => [] end.
Definition propose_memory_pointer_address_parameters layout sources :=
  nodup peq (filter (fun identifier => negb (existsb (Pos.eqb identifier) layout))
    (flat_map memory_pointer_statement_address_registers sources)).
Definition memory_param_propose_caps nest parameters parameter_caps scalars operations :=
  let dimensions := length (memory_nest_iterators nest) in
  let valid := fun caps => forallb (memory_multi_pointer_compute_check (caps++parameter_caps)
    (memory_nest_iterators nest++parameters) scalars 1024) operations in
  memory_vector_grow_axes dimensions valid O (repeat 1 dimensions).
Definition describe_memory_param_axis_at source (profile : list Z * list Z) :=
  let nest := propose_memory_source_nest (progress_syntax_size source) source in
  let statements := flatten_region (memory_nest_leaf nest) in
  let parameters := propose_memory_pointer_address_parameters (memory_nest_iterators nest) statements in
  if Nat.leb 1 (length (memory_nest_iterators nest)) && Nat.leb 1 (length parameters) then
    let layout := memory_nest_iterators nest++parameters in
    let scalars := propose_memory_pointer_scalars layout statements in
    match propose_memory_scalar_pointer_computes 1024 layout scalars statements with
    | Some (operation::operations) => check_memory_param_pointer_region source nest (fst profile) parameters (snd profile)
        (memory_multi_pointer_operation_identifiers (operation::operations)) 1024 scalars (operation::operations)
    | _ => None end
  else None.
Definition propose_memory_param_axis_profiles source :=
  let nest := propose_memory_source_nest (progress_syntax_size source) source in
  let statements := flatten_region (memory_nest_leaf nest) in
  let parameters := propose_memory_pointer_address_parameters (memory_nest_iterators nest) statements in
  let layout := memory_nest_iterators nest++parameters in
  let scalars := propose_memory_pointer_scalars layout statements in
  match propose_memory_scalar_pointer_computes 1024 layout scalars statements with
  | Some operations => flat_map (fun parameter_cap =>
      let parameter_caps := repeat parameter_cap (length parameters) in
      map (fun caps => (caps,parameter_caps))
        (memory_vector_cap_profiles (memory_param_propose_caps nest parameters parameter_caps scalars operations))) [64;16;8;4;1]
  | None => [] end.
Fixpoint check_memory_param_axis_profiles source
  (check : memory_param_pointer_region_package source -> CoreAlarmed.Base.imp (option statement)) profiles :=
  match profiles with
  | [] => pure None
  | profile::rest => match describe_memory_param_axis_at source profile with
    | Some package => BIND candidate <- check package -;
        match candidate with Some target => pure (Some target) | None => check_memory_param_axis_profiles check rest end
    | None => check_memory_param_axis_profiles check rest end end.
Theorem check_memory_param_axis_profiles_sound source live
  (check : memory_param_pointer_region_package source -> CoreAlarmed.Base.imp (option statement)) :
  (forall package target, mayReturn (check package) (Some target) -> projected_region_contract live source target) ->
  forall profiles target, mayReturn (check_memory_param_axis_profiles check profiles) (Some target) ->
    projected_region_contract live source target.
Proof.
  intros CHECK profiles; induction profiles as [|profile profiles IH]; intros target RUN; cbn [check_memory_param_axis_profiles] in RUN.
  - apply mayReturn_pure in RUN; discriminate.
  - destruct (describe_memory_param_axis_at source profile) as [package|].
    + bind_imp_destruct RUN candidate ACCEPTED; destruct candidate as [candidate|].
      * apply mayReturn_pure in RUN; inversion RUN; subst target; apply CHECK with (package := package); exact ACCEPTED.
      * apply IH; exact RUN.
    + apply IH; exact RUN.
Qed.
Print Assumptions check_memory_param_axis_profiles_sound.
