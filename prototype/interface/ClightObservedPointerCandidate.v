From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightCondition ClightPrivateRegion ClightPrivatePool ClightTempFootprint.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryLoops GuardMemoryRecursiveSource GuardMemoryRecursiveCandidate
  GuardMemoryRecursiveChecker GuardMemoryVectorChecker GuardMemoryTiledCompiler GuardMemoryParamPointerBounds GuardMemoryParamPointerSyntax
  GuardMemoryLinearPointerSyntax GuardMemoryParamPointerProjectedCandidate GuardMemoryParamAxisGuard GuardMemoryParamAxisFrame
  GuardMemoryParamAxisCompiler.
From GuardInterface Require Import GuardInterface ClightPrivateScan ClightPrivateScanHost ClightPrivateScanPreservation
  ClightParamPointerPreservation ClightSourceObservation ClightPrivateScanShortcut ClightParamPointerEnvelope
  ClightObservedPointerPreservation.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

(** The existing checked lowering exposes a witness binding its actual AST,
    condition and conditional candidate proof. No second candidate validator
    is introduced for the symbolic shortcut. *)
Lemma checked_pointer_scan_rule_witness live pool source
  (package : memory_param_pointer_region_package source) candidate check target :
  (mayReturn check true -> memory_bounded_candidate_certificate
    (memory_param_static_bounds (param_pointer_region_limits package) (param_pointer_region_parameter_limits package)
      (length (param_pointer_region_scalars package)))
    (length (memory_nest_iterators (param_pointer_region_nest package)))
    (memory_param_pointer_region_arity package) (memory_param_pointer_region_instructions package)
    (memory_param_pointer_region_context package) candidate) ->
  mayReturn (check_private_scan_param_pointer_candidate live pool package candidate check) (Some target) ->
  exists rule : private_scan_preserving_rule live source,
    target = private_scan_select (scan_body (scan_condition rule)) (scan_result (scan_condition rule))
      (scan_candidate rule) source /\
    scan_domain rule = memory_param_pointer_runtime_domain package /\
    scan_premise rule = memory_param_pointer_runtime_presumption package.
Proof.
  intros CERT; unfold check_private_scan_param_pointer_candidate.
  destruct (Nat.leb (length (memory_linear_pointer_accesses (param_pointer_region_code package))) 32%nat);
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct pool as [|[result ty] private]; [intro RUN; apply mayReturn_pure in RUN; discriminate|].
  destruct (private_counter_pairs private) as [pairs|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (nth_error pairs (length (memory_nest_iterators (param_pointer_region_nest package)))) as [[flag spare]|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (memory_param_axis_pointer_guard_names_check package live
    (map fst (firstn (length (memory_nest_iterators (param_pointer_region_nest package))) pairs))
    (map snd (firstn (length (memory_nest_iterators (param_pointer_region_nest package))) pairs)) flag) eqn:NAMES;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (in_dec peq result _) as [|RESULT]; [intro RUN; apply mayReturn_pure in RUN; discriminate|].
  destruct (compile_memory_param_pointer_region_candidate package live pairs candidate) as [code|] eqn:COMPILE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN valid VALID; apply mayReturn_pure in RUN.
  destruct valid; [inversion RUN; subst target|discriminate].
  exists (@param_pointer_scan_preserving_rule source package live pairs candidate code _ _ flag result
    NAMES RESULT COMPILE (CERT VALID)); repeat split; reflexivity.
Qed.

Definition observed_pointer_target_of_checked source (package : memory_param_pointer_region_package source) loads original :=
  match original with
  | Ssequence _ (Sifthenelse _ candidate _) =>
    Some (Ssequence (source_load_prefix loads) (tree_statement (param_pointer_envelope_tree package) candidate original))
  | _ => None end.

Definition check_observed_param_pointer_candidate live pool source
  (package : memory_param_pointer_region_package source) loads candidate check :=
  if source_observations_check (param_pointer_region_pointers package) loads then
    BIND original <- check_private_scan_param_pointer_candidate live pool package candidate check -;
    pure (match original with Some original => observed_pointer_target_of_checked package loads original | None => None end)
  else pure None.

Theorem check_observed_param_pointer_candidate_sound live pool source
  (package : memory_param_pointer_region_package source) loads candidate check target :
  (mayReturn check true -> memory_bounded_candidate_certificate
    (memory_param_static_bounds (param_pointer_region_limits package) (param_pointer_region_parameter_limits package)
      (length (param_pointer_region_scalars package)))
    (length (memory_nest_iterators (param_pointer_region_nest package)))
    (memory_param_pointer_region_arity package) (memory_param_pointer_region_instructions package)
    (memory_param_pointer_region_context package) candidate) ->
  mayReturn (check_observed_param_pointer_candidate live pool package loads candidate check) (Some target) ->
  PrivateRegion.projected_region_contract live (Ssequence (source_load_prefix loads) source) target.
Proof.
  intros CERT; unfold check_observed_param_pointer_candidate.
  destruct (source_observations_check (param_pointer_region_pointers package) loads) eqn:OBSERVATIONS;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN original OLD; apply mayReturn_pure in RUN.
  destruct original as [original|]; [|discriminate].
  destruct (@checked_pointer_scan_rule_witness live pool source package candidate check original CERT OLD)
    as [rule [TARGET [DOMAIN PREMISE]]].
  rewrite TARGET in RUN; unfold observed_pointer_target_of_checked,private_scan_select in RUN.
  injection RUN as <-.
  destruct (@source_observations_check_sound (param_pointer_region_pointers package) loads OBSERVATIONS) as [COVER FRESH].
  apply (@observed_param_pointer_region_contract live source package rule loads DOMAIN PREMISE COVER FRESH).
Qed.

Print Assumptions checked_pointer_scan_rule_witness.
Print Assumptions check_observed_param_pointer_candidate_sound.
