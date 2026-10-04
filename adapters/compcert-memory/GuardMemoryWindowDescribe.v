From Stdlib Require Import List Bool ZArith.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightStructuredProgress ClightStraightLine ClightPrivateRegion.
From GuardMemory Require Import GuardMemoryNaryCompute GuardMemoryMultiPointerIdentifiers GuardMemoryScalarPointerComputeSyntax
  GuardMemoryRecursiveSource GuardMemoryRecursiveSyntax GuardMemoryVectorAxisDescribe GuardMemoryParamAxisDescribe.
From GuardMemory Require Import GuardMemoryWindowSyntax GuardMemoryWindowCheck GuardMemoryWindowPackage GuardMemoryWindowPackageBuilder GuardMemoryWindowStartedPackage.
Import CoreAlarmed ListNotations PrivateRegion.
Set Implicit Arguments.
Local Open Scope Z_scope.
Definition describe_window_at source (profile : list Z * Z) :=
  let nest := propose_memory_source_nest (progress_syntax_size source) source in
  let statements := flatten_region (memory_nest_leaf nest) in
  let parameters := propose_memory_pointer_address_parameters (memory_nest_iterators nest) statements in
  let layout := memory_nest_iterators nest++parameters in
  let scalars := propose_memory_pointer_scalars layout statements in
  match propose_memory_scalar_pointer_computes 1024 layout scalars statements with
  | Some (operation::operations) =>
      match make_window_region_package source nest (fst profile) (-snd profile)
        parameters (repeat (-snd profile,snd profile+1) (length parameters))
        (memory_multi_pointer_operation_identifiers (operation::operations)) (-1024) 1024 scalars (operation::operations) with
      | Some package => make_window_started_package package
      | None => None end
  | _ => None end.
Definition propose_window_profiles source :=
  let nest := propose_memory_source_nest (progress_syntax_size source) source in
  let statements := flatten_region (memory_nest_leaf nest) in
  let parameters := propose_memory_pointer_address_parameters (memory_nest_iterators nest) statements in
  let layout := memory_nest_iterators nest++parameters in
  let scalars := propose_memory_pointer_scalars layout statements in
  let dimensions := length (memory_nest_iterators nest) in
  match propose_memory_scalar_pointer_computes 1024 layout scalars statements with
  | Some operations => flat_map (fun radius =>
      let parameter_bounds := repeat (-radius,radius+1) (length parameters) in
      let valid := fun caps => forallb (window_compute_check
        (window_source_coordinate_bounds (-radius) caps++parameter_bounds) (-1024) 1024 layout scalars) operations in
      map (fun caps => (caps,radius)) (memory_vector_cap_profiles
        (memory_vector_grow_axes dimensions valid O (repeat 1 dimensions)))) [64;16;8;4;1]
  | None => [] end.
Fixpoint check_window_profiles source
  (check : window_started_package source -> CoreAlarmed.Base.imp (option statement)) profiles :=
  match profiles with
  | [] => pure None
  | profile::rest => match describe_window_at source profile with
    | Some package => BIND candidate <- check package -;
        match candidate with Some target => pure (Some target) | None => check_window_profiles check rest end
    | None => check_window_profiles check rest end end.
Theorem check_window_profiles_sound source live
  (check : window_started_package source -> CoreAlarmed.Base.imp (option statement)) :
  (forall package target, mayReturn (check package) (Some target) -> projected_region_contract live source target) ->
  forall profiles target, mayReturn (check_window_profiles check profiles) (Some target) -> projected_region_contract live source target.
Proof.
  intros CHECK profiles; induction profiles as [|profile profiles IH]; intros target RUN; cbn [check_window_profiles] in RUN.
  - apply mayReturn_pure in RUN; discriminate.
  - destruct (describe_window_at source profile) as [package|].
    + bind_imp_destruct RUN candidate ACCEPTED; destruct candidate as [candidate|].
      * apply mayReturn_pure in RUN; inversion RUN; subst target; apply CHECK with (package := package); exact ACCEPTED.
      * apply IH; exact RUN.
    + apply IH; exact RUN.
Qed.
Print Assumptions check_window_profiles_sound.
