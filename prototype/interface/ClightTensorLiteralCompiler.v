From Stdlib Require Import List Bool.
From compcert.lib Require Import Coqlib Integers.
From compcert.common Require Import AST Errors Smallstep.
From compcert.cfrontend Require Import Ctypes Clight Csyntax Csem Cstrategy
  SimplExpr SimplExprproof SimplLocals SimplLocalsproof.
From compcert.driver Require Import Compiler.
From compcert.x86 Require Import Asm.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightPrivateRegion ClightPrivatePool ClightTempFootprint
  ClightRegionProgress GuardCompiler.
From GuardMemory Require Import GuardMemoryTensorSource GuardMemoryNamedCompiler GuardMemoryTiledCompiler GuardMemoryCompiler.
From GuardInterface Require Import ClightCheckPlanFrame ClightLiteralBoundPreparation ClightTensorLiteralPreservation
  ClightTensorRegionPackage ClightTensorRegionPreservation ClightTensorRegionCompiler
  ClightMaterializedCheck ClightSharedGuard ClightExpressionRegionHost.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

(** The source chooser returns only an integer literal. Source and candidate
    descriptions remain untrusted data, checked on the actual canonical AST. *)
Definition tensor_literal_proposer:=Clight.statement->option int.
Definition check_tensor_literal_region live pool(choose:tensor_literal_proposer)
    (describe:tensor_description_proposer)(propose:tensor_candidate_proposer)source : Base.imp(option Clight.statement) :=
  match pool,choose source with
  | (helper,helper_type)::(result,result_type)::private,Some upper=>
    if type_eq helper_type type_int32s then if type_eq result_type type_int32s then
    if Bool.bool_dec(check_plan_frameable source)true then if Bool.bool_dec(quiet_statement source)true then
    if in_dec peq helper(statement_temps source++live)then pure None else
    let canonical:=literal_tests_prepare helper upper source in
    match describe canonical with
    | Some description=>match check_tensor_region_description canonical description,private_counter_pairs private with
      | Some package,Some pairs=>
        let tree:=tensor_region_guard package in
        let ports:=tensor_literal_ports live source helper tree in
        if in_dec peq result(helper::ports)then pure None else
        match describe_materialized_check(tensor_literal_check_body helper upper tree result)(shared_guard_choice result) with
        | Some test=>match propose[tensor_source_instruction(tensor_operation package)]with
          | Some proposal=>BIND code <- check_tensor_region_candidate package live pairs proposal -;
            pure(match code with Some code=>Some(materialized_select test
              (tensor_literal_candidate helper upper(tensor_region_branch package code))source)|None=>None end)
          | None=>pure None end
        | None=>pure None end
      | _,_=>pure None end
    | None=>pure None end
    else pure None else pure None else pure None else pure None
  | _,_=>pure None end.

Theorem check_tensor_literal_region_sound live pool choose describe propose source target :
  mayReturn(check_tensor_literal_region live pool choose describe propose source)(Some target) ->
  PrivateRegion.projected_region_contract live source target.
Proof.
  unfold check_tensor_literal_region.
  destruct pool as [|[helper ht][|[result rt]private]]; try(intro RUN; apply mayReturn_pure in RUN; discriminate).
  destruct(choose source)as [upper|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(type_eq ht type_int32s), (type_eq rt type_int32s);
    try(intro RUN; apply mayReturn_pure in RUN; discriminate).
  destruct(Bool.bool_dec(check_plan_frameable source)true)as [FRAMEABLE|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(Bool.bool_dec(quiet_statement source)true)as [QUIET|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(in_dec peq helper(statement_temps source++live))as [|FRESH]; [intro RUN; apply mayReturn_pure in RUN; discriminate|].
  destruct(describe(literal_tests_prepare helper upper source))as [description|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(check_tensor_region_description(literal_tests_prepare helper upper source)description)as [package|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(private_counter_pairs private)as [pairs|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(in_dec peq result(helper::tensor_literal_ports live source helper(tensor_region_guard package)))as [|RESULT];
    [intro RUN; apply mayReturn_pure in RUN; discriminate|].
  destruct(describe_materialized_check(tensor_literal_check_body helper upper(tensor_region_guard package)result)
    (shared_guard_choice result))as [test|]eqn:TEST; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(propose[tensor_source_instruction(tensor_operation package)])as [proposal|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN generated CHECK; apply mayReturn_pure in RUN.
  destruct generated as [code|]; [|discriminate]; inversion RUN; subst target.
  destruct(@describe_materialized_check_exact _ _ _ TEST)as [BODY CONDITION].
  exact(@tensor_literal_region_contract live source helper upper package FRAMEABLE QUIET FRESH result RESULT
    test BODY CONDITION pairs proposal code CHECK).
Qed.

Fixpoint checked_tensor_literal_regions live pool choose describe propose sources := match sources with
| []=>pure []
| source::rest=>BIND target <- check_tensor_literal_region live pool choose describe propose source -;
  BIND table <- checked_tensor_literal_regions live pool choose describe propose rest -;
  pure(match target with Some target=>(source,target)::table|None=>table end)end.
Theorem checked_tensor_literal_regions_sound live pool choose describe propose sources table :
  mayReturn(checked_tensor_literal_regions live pool choose describe propose sources)table ->
  Forall(fun pair=>PrivateRegion.projected_region_contract live(fst pair)(snd pair))table.
Proof.
  revert table; induction sources as [|source sources IH]; intros table RUN; cbn in RUN.
  - apply mayReturn_pure in RUN; subst; constructor.
  - bind_imp_destruct RUN target CHECK; bind_imp_destruct RUN rest REST; apply mayReturn_pure in RUN.
    destruct target; subst; [constructor; [eapply check_tensor_literal_region_sound; exact CHECK|]|]; apply IH; exact REST.
Qed.

Definition compile_tensor_literal_regions choose describe propose private_count(program:Csyntax.program) : Base.imp(res Asm.program) :=
  match SimplExpr.transl_program program with
  | Error errors=>pure(Error errors)
  | OK clight=>match SimplLocals.transf_program clight with
    | Error errors=>pure(Error errors)
    | OK normalized=>let live:=program_temps normalized in let pool:=propose_private_names live private_count in
      BIND table <- checked_tensor_literal_regions live pool choose describe propose(memory_program_candidates normalized) -;
      pure(compile_clight_tail(Compiler.print Compiler.print_Clight(apply_expression_region_table pool table normalized)))end end.

Theorem tensor_literal_cstrategy_forward choose describe propose private_count program target :
  mayReturn(compile_tensor_literal_regions choose describe propose private_count program)(OK target) ->
  forward_simulation(Cstrategy.semantics program)(Asm.semantics target).
Proof.
  unfold compile_tensor_literal_regions; destruct(SimplExpr.transl_program program)as [clight|errors]eqn:P1;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(SimplLocals.transf_program clight)as [normalized|errors]eqn:P2;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN table TABLE; apply mayReturn_pure in RUN; rewrite Compiler.print_identity in RUN.
  eapply compose_forward_simulations.
  { eapply SimplExprproof.transl_program_correct; eauto using SimplExprproof.transf_program_match. }
  eapply compose_forward_simulations.
  { eapply SimplLocalsproof.transf_program_correct; eauto using SimplLocalsproof.match_transf_program. }
  eapply compose_forward_simulations.
  { apply apply_expression_region_table_correct; eapply checked_tensor_literal_regions_sound; exact TABLE. }
  eapply clight_tail_correct; exact RUN.
Qed.
Theorem compile_tensor_literal_regions_correct choose describe propose private_count program target :
  mayReturn(compile_tensor_literal_regions choose describe propose private_count program)(OK target) ->
  backward_simulation(Csem.semantics program)(Asm.semantics target).
Proof.
  intro RUN; apply compose_backward_simulation with(atomic(Cstrategy.semantics program)).
  - eapply sd_traces; eapply Asm.semantics_determinate.
  - apply factor_backward_simulation.
    + apply Cstrategy.strategy_simulation.
    + apply Csem.semantics_single_events.
    + eapply ssr_well_behaved; eapply Cstrategy.semantics_strongly_receptive.
  - apply forward_to_backward_simulation.
    + apply factor_forward_simulation.
      * eapply tensor_literal_cstrategy_forward; exact RUN.
      * eapply sd_traces; eapply Asm.semantics_determinate.
    + apply atomic_receptive; apply Cstrategy.semantics_strongly_receptive.
    + apply Asm.semantics_determinate.
Qed.
Print Assumptions check_tensor_literal_region_sound.
Print Assumptions checked_tensor_literal_regions_sound.
Print Assumptions tensor_literal_cstrategy_forward.
Print Assumptions compile_tensor_literal_regions_correct.
