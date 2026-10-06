From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightPrivateRegion.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryLoops GuardMemoryRecursiveSource
  GuardMemoryRecursiveCandidate GuardMemoryRecursiveChecker GuardMemoryScalarChecker GuardMemoryScalarLoops
  GuardMemoryVectorChecker
  GuardMemoryTiledCompiler
  GuardMemoryMultiPointerSyntax GuardMemoryMultiPointerCompiler GuardMemoryParamPointerBounds
  GuardMemoryLinearPointerSyntax
  GuardMemoryParamPointerSyntax GuardMemoryParamPointerHeader GuardMemoryParamPointerProjectedCandidate
  GuardMemoryParamAxisFrame GuardMemoryParamAxisGuard GuardMemoryParamAxisCompiler GuardMemoryProjectedCondition.
From GuardInterface Require Import ClightPrivateScan ClightPrivateScanHost ClightPrivateScanPreservation
  ClightParamPointerEntryFacts ClightParamPointerCertificate.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition param_pointer_scan_target source (package : memory_param_pointer_region_package source)
  left right flag result code :=
  private_scan_select (memory_param_axis_pointer_guard_statement package left right flag) result
    (memory_recursive_candidate code (param_pointer_region_nest package)) source.

Section RULE.
Variable source : statement.
Variable package : memory_param_pointer_region_package source.
Variable live : list ident.
Variable pairs : list (ident * ident).
Variable candidate : L.stmt.
Variable code : statement.
Variable left right : list ident.
Variable flag result : ident.
Hypothesis NAMES : memory_param_axis_pointer_guard_names_check package live left right flag = true.
Hypothesis RESULT : ~ In result
  (statement_temps (memory_param_axis_pointer_guard_statement package left right flag) ++
   memory_param_axis_pointer_guard_protected package live).
Hypothesis COMPILE : compile_memory_param_pointer_region_candidate package live pairs candidate = Some code.
Hypothesis CANDIDATE : memory_bounded_candidate_certificate
  (memory_param_static_bounds (param_pointer_region_limits package) (param_pointer_region_parameter_limits package)
    (length (param_pointer_region_scalars package)))
  (length (memory_nest_iterators (param_pointer_region_nest package)))
  (memory_param_pointer_region_arity package) (memory_param_pointer_region_instructions package)
  (memory_param_pointer_region_context package) candidate.

Definition param_pointer_scan_preserving_rule : private_scan_preserving_rule live source.
Proof.
  set (old := @memory_param_pointer_projected_candidate_rule source package live pairs candidate code COMPILE CANDIDATE).
  refine {| scan_candidate := memory_recursive_candidate code (param_pointer_region_nest package);
    scan_condition := @param_pointer_scan_test source package live left right flag result RESULT;
    scan_domain := memory_param_pointer_runtime_domain package;
    scan_premise := memory_param_pointer_runtime_presumption package;
    scan_ports := memory_param_axis_pointer_guard_protected package live;
    scan_writes := projected_rule_writes old; scan_source_writes := projected_rule_source_writes old |}.
  - intros identifier MEMBER; unfold memory_param_axis_pointer_guard_protected.
    repeat (apply in_or_app; right); exact MEMBER.
  - intro temps.
    destruct (@memory_param_axis_pointer_guard_names_sound source package live left right flag NAMES)
      as [LEFT [RIGHT [UNIQUE [LEFT_PARAM [RIGHT_PARAM [FRESH FLAG]]]]]].
    exact (@param_pointer_scan_certificate source package live left right flag result
      LEFT RIGHT UNIQUE LEFT_PARAM RIGHT_PARAM FRESH FLAG RESULT _ _ (scan_public_observe live)).
  - intros entry checked DOMAIN PREMISE [GE [ENV [MEMORY FRAME]]].
    destruct entry as [ge locals original memory], checked as [current_ge current_locals current current_memory].
    cbn [entry_ge entry_env entry_memory entry_temps] in *; subst.
    apply (proj2 (@param_pointer_presumption_temp_frame source package ge locals memory original current live
      (proj1 DOMAIN) FRAME)); exact PREMISE.
  - exact (projected_rule_local old).
  - exact (projected_rule_entry old).
Defined.

Theorem param_pointer_scan_target_sound :
  PrivateRegion.projected_region_contract live source
    (param_pointer_scan_target package left right flag result code).
Proof.
  exact (@private_scan_preserving_region_contract live source param_pointer_scan_preserving_rule).
Qed.
End RULE.

(** The result consumes its own fresh pool slot. The remaining pairs are
    shared by candidate lowering and the two-coordinate check; the candidate
    certificate permits arbitrary initial values of these private counters. *)
Definition check_private_scan_param_pointer_candidate live pool source
  (package : memory_param_pointer_region_package source) candidate (check : CoreAlarmed.Base.imp bool) :
  CoreAlarmed.Base.imp (option statement) :=
  if Nat.leb (length (memory_linear_pointer_accesses (param_pointer_region_code package))) 32%nat then
  match pool with
  | (result,_)::private => match private_counter_pairs private with
    | Some pairs =>
      let dimensions := length (memory_nest_iterators (param_pointer_region_nest package)) in
      let selected := firstn dimensions pairs in
      let left := map fst selected in let right := map snd selected in
      match nth_error pairs dimensions with
      | Some (flag,_) =>
        if memory_param_axis_pointer_guard_names_check package live left right flag then
          if in_dec peq result
            (statement_temps (memory_param_axis_pointer_guard_statement package left right flag) ++
             memory_param_axis_pointer_guard_protected package live) then pure None
          else match compile_memory_param_pointer_region_candidate package live pairs candidate with
            | Some code => BIND valid <- check -;
                pure (if valid then Some (param_pointer_scan_target package left right flag result code) else None)
            | None => pure None end
        else pure None
      | None => pure None end
    | None => pure None end
  | _ => pure None end else pure None.

Theorem check_private_scan_param_pointer_candidate_sound live pool source
  (package : memory_param_pointer_region_package source) candidate check target :
  (mayReturn check true -> memory_bounded_candidate_certificate
    (memory_param_static_bounds (param_pointer_region_limits package) (param_pointer_region_parameter_limits package)
      (length (param_pointer_region_scalars package)))
    (length (memory_nest_iterators (param_pointer_region_nest package)))
    (memory_param_pointer_region_arity package) (memory_param_pointer_region_instructions package)
    (memory_param_pointer_region_context package) candidate) ->
  mayReturn (check_private_scan_param_pointer_candidate live pool package candidate check) (Some target) ->
  PrivateRegion.projected_region_contract live source target.
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
  exact (@param_pointer_scan_target_sound source package live pairs candidate code _ _ flag result
    NAMES RESULT COMPILE (CERT VALID)).
Qed.

Print Assumptions param_pointer_scan_preserving_rule.
Print Assumptions param_pointer_scan_target_sound.
Print Assumptions check_private_scan_param_pointer_candidate_sound.
