From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST Errors Smallstep.
From compcert.cfrontend Require Import Ctypes Clight Csyntax Csem Cstrategy
  SimplExpr SimplExprproof SimplLocals SimplLocalsproof.
From compcert.driver Require Import Compiler.
From compcert.x86 Require Import Asm.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightPrivateRegion ClightPrivatePool ClightTempFootprint
  ClightRegionProgress ClightStraightLine GuardCompiler.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryNamedCompiler GuardMemoryTiledCompiler GuardMemoryCompiler.
From GuardMemory Require Import GuardMemoryRecursiveSource.
From GuardInterface Require Import ClightGuardRealization ClightSharedGuard ClightReadonlyRuleEmbedding
  ClightReadonlyPreservationKernel ClightTensorRegionPackage ClightTensorRegionPreservation.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

Definition tensor_description_proposer := Clight.statement -> option tensor_region_description.
Definition tensor_candidate_proposer := list memory_instruction -> option tensor_region_candidate.
Definition tensor_dispatch_pool(shared:bool)(pool:list(ident*type)) :=
  if shared then match pool with
    | (result,ty)::rest=>if type_eq ty type_int32s then Some(result,rest)else None
    | []=>None end else Some(1%positive,pool).
Definition tensor_region_shared_target source(package:tensor_region_package source)code result :=
  shared_guard_statement(tensor_region_guard package)result(tensor_region_branch package code)source.

Definition choose_tensor_region_lowering(shared:bool)live source(package:tensor_region_package source)code result : option Clight.statement :=
  if shared then
    if Bool.bool_dec(quiet_statement(tensor_region_branch package code))true then
      if in_dec peq result(statement_temps(tensor_region_branch package code)++statement_temps source++live)then None
      else Some(tensor_region_shared_target package code result)
    else None
  else Some(tensor_region_direct_target package code).

Theorem choose_tensor_region_lowering_sound shared live source(package:tensor_region_package source)pool proposal code result target :
  mayReturn(check_tensor_region_candidate package live pool proposal)(Some code) ->
  choose_tensor_region_lowering shared live package code result=Some target ->
  PrivateRegion.projected_region_contract live source target.
Proof.
  intros CHECK; unfold choose_tensor_region_lowering; destruct shared.
  - destruct(Bool.bool_dec(quiet_statement(tensor_region_branch package code))true)as [QUIET|]; [|discriminate].
    destruct(in_dec peq result(statement_temps(tensor_region_branch package code)++statement_temps source++live))as [|FRESH]; [discriminate|].
    intro SAME; inversion SAME; subst target.
    exact(@readonly_kernel_realized_region_contract live source(@tensor_region_preserving_rule source package live pool proposal code CHECK)
      (@shared_normal_realization live(tensor_region_guard package)(tensor_region_branch package code)source result
        (statement_temps(tensor_region_branch package code))(memory_nest_iterators(tensor_nest package))
        (@quiet_source_write_bound(tensor_region_branch package code)QUIET)(tensor_region_source_writes package)FRESH)).
  - intro SAME; inversion SAME; subst target; eapply tensor_region_direct_contract; exact CHECK.
Qed.

Definition check_tensor_region shared live pool(describe:tensor_description_proposer)(propose:tensor_candidate_proposer)source :
    Base.imp(option Clight.statement) :=
  match tensor_dispatch_pool shared pool,describe source with
  | Some(result,private),Some description=>match private_counter_pairs private,check_tensor_region_description source description with
    | Some pairs,Some package=>match propose[GuardMemoryTensorSource.tensor_source_instruction(tensor_operation package)]with
      | Some proposal=>BIND code <- check_tensor_region_candidate package live pairs proposal -;
        pure(match code with Some code=>choose_tensor_region_lowering shared live package code result|None=>None end)
      | None=>pure None end
    | _,_=>pure None end
  | _,_=>pure None end.

Theorem check_tensor_region_sound shared live pool describe propose source target :
  mayReturn(check_tensor_region shared live pool describe propose source)(Some target) ->
  PrivateRegion.projected_region_contract live source target.
Proof.
  unfold check_tensor_region.
  destruct(tensor_dispatch_pool shared pool)as [[result private]|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(describe source)as [description|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(private_counter_pairs private)as [pairs|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(check_tensor_region_description source description)as [package|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(propose[GuardMemoryTensorSource.tensor_source_instruction(tensor_operation package)])as [proposal|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN generated CHECK; apply mayReturn_pure in RUN.
  destruct generated as [code|]; [|discriminate].
  eapply choose_tensor_region_lowering_sound; [exact CHECK|exact RUN].
Qed.

Fixpoint checked_tensor_regions shared live pool describe propose sources : Base.imp(list(Clight.statement*Clight.statement)) :=
  match sources with
  | []=>pure []
  | source::rest=>BIND target <- check_tensor_region shared live pool describe propose source -;
    BIND table <- checked_tensor_regions shared live pool describe propose rest -;
    pure(match target with Some target=>(source,target)::table|None=>table end)end.
Theorem checked_tensor_regions_sound shared live pool describe propose sources table :
  mayReturn(checked_tensor_regions shared live pool describe propose sources)table ->
  Forall(fun pair=>PrivateRegion.projected_region_contract live(fst pair)(snd pair))table.
Proof.
  revert table; induction sources as [|source sources IH]; intros table RUN; cbn in RUN.
  - apply mayReturn_pure in RUN; subst; constructor.
  - bind_imp_destruct RUN target TARGET; bind_imp_destruct RUN rest REST; apply mayReturn_pure in RUN.
    destruct target as [target|]; subst; [constructor; [eapply check_tensor_region_sound; exact TARGET|]|]; apply IH; exact REST.
Qed.

(** Installation uses the existing checked private pool, source scopes,
    recursive counted-loop progress and continuation simulation. The table is
    produced from actual input ASTs, not caller-supplied semantic callbacks. *)
Definition apply_tensor_region_table := apply_memory_tiled_table.
Theorem apply_tensor_region_table_correct pool table program :
  Forall(fun pair=>PrivateRegion.projected_region_contract(program_temps program)(fst pair)(snd pair))table ->
  forward_simulation(Clight.semantics2 program)(Clight.semantics2(apply_tensor_region_table pool table program)).
Proof. apply apply_memory_tiled_table_correct. Qed.

Definition compile_tensor_regions shared describe propose private_count(program:Csyntax.program) : Base.imp(res Asm.program) :=
  match SimplExpr.transl_program program with
  | Error errors=>pure(Error errors)
  | OK clight=>match SimplLocals.transf_program clight with
    | Error errors=>pure(Error errors)
    | OK normalized=>let live:=program_temps normalized in let pool:=propose_private_names live private_count in
      BIND table <- checked_tensor_regions shared live pool describe propose(memory_program_candidates normalized) -;
      pure(compile_clight_tail(Compiler.print Compiler.print_Clight(apply_tensor_region_table pool table normalized)))end end.

Theorem tensor_regions_cstrategy_forward shared describe propose private_count program target :
  mayReturn(compile_tensor_regions shared describe propose private_count program)(OK target) ->
  forward_simulation(Cstrategy.semantics program)(Asm.semantics target).
Proof.
  unfold compile_tensor_regions; destruct(SimplExpr.transl_program program)as [clight|errors]eqn:P1;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(SimplLocals.transf_program clight)as [normalized|errors]eqn:P2;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN table TABLE; apply mayReturn_pure in RUN; rewrite Compiler.print_identity in RUN.
  eapply compose_forward_simulations.
  { eapply SimplExprproof.transl_program_correct; eauto using SimplExprproof.transf_program_match. }
  eapply compose_forward_simulations.
  { eapply SimplLocalsproof.transf_program_correct; eauto using SimplLocalsproof.match_transf_program. }
  eapply compose_forward_simulations.
  { apply apply_tensor_region_table_correct; eapply checked_tensor_regions_sound; exact TABLE. }
  eapply clight_tail_correct; exact RUN.
Qed.
Theorem compile_tensor_regions_correct shared describe propose private_count program target :
  mayReturn(compile_tensor_regions shared describe propose private_count program)(OK target) ->
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
      * eapply tensor_regions_cstrategy_forward; exact RUN.
      * eapply sd_traces; eapply Asm.semantics_determinate.
    + apply atomic_receptive; apply Cstrategy.semantics_strongly_receptive.
    + apply Asm.semantics_determinate.
Qed.
Print Assumptions choose_tensor_region_lowering_sound.
Print Assumptions check_tensor_region_sound.
Print Assumptions checked_tensor_regions_sound.
Print Assumptions apply_tensor_region_table_correct.
Print Assumptions compile_tensor_regions_correct.
