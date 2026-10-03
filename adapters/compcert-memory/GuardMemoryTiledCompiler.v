From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST Errors Smallstep.
From compcert.cfrontend Require Import Ctypes Clight Csyntax Csem Cstrategy SimplExpr SimplExprproof
  SimplLocals SimplLocalsproof.
From compcert.driver Require Import Compiler.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightGuard ClightCondition ClightPrivateRule ClightPrivateRegion
  ClightPrivateRegionProof ClightPrivatePool ClightTempFootprint ClightTempScope
  ClightStructuredProgress ClightRectangularSelector ClightRectangularStore
  ClightRectangularGuard ClightRectangularRegion ClightRectangularLoops GuardCompiler
  ClightFrontendLoopProtocol ClightSharedRegion ClightSyntaxEquality.
From GuardMemory Require Import GuardMemoryClightRectangles GuardMemoryCompiler GuardMemoryTiledClight GuardMemoryModeTiledClight.
Import CoreAlarmed ListNotations PrivateRegion.
Import Clight.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint private_counter_pairs (pool : list (ident * type)) : option (list (ident * ident)) :=
  match pool with
  | [] => Some []
  | (counter,ty)::(bound,bty)::rest =>
    if type_eq ty type_int32s then if type_eq bty type_int32s then
      match private_counter_pairs rest with Some pairs => Some ((counter,bound)::pairs) | None => None end
    else None else None
  | _ => None end.

Record memory_tiling_package source := MemoryTilingPackage {
  tiling_mode : rectangle_memory_mode;
  tiling_description : rectangle_description;
  tiling_syntax : memory_rectangle_certificate source tiling_mode tiling_description
}.
Definition describe_memory_tiling source : option (memory_tiling_package source) :=
  match describe_memory_rectangle source with
  | Some package => Some (@MemoryTilingPackage source (package_mode package)
      (package_description package) (package_syntax package))
  | None => None end.
Definition memory_tiled_target source (package : memory_tiling_package source) code :=
  let d := tiling_description package in
  shared_guarded_statement (rectangle_guard_tree (described_shape d)
    (rectangle_row d) (rectangle_bound d) (rectangle_inner_bound d))
    (rectangle_tiled_candidate code (rectangle_row d) (rectangle_bound d)
      (rectangle_column d) (rectangle_inner_bound d)) source.

Theorem memory_tiled_target_sound source (package : memory_tiling_package source) live pairs bi bj code :
  0 < bi -> 0 < bj ->
  compile_rectangle_mode_tiled (tiling_mode package) (described_shape (tiling_description package))
    (described_array (tiling_description package)) (rectangle_bound (tiling_description package))
    (rectangle_inner_bound (tiling_description package)) live pairs bi bj = Some code ->
  mayReturn (checked_rectangle_mode_tiling (tiling_mode package) (described_shape (tiling_description package)) bi bj) true ->
  projected_region_contract live source (memory_tiled_target package code).
Proof.
  destruct package as [mode d CERT]; cbn; intros BI BJ COMPILE CHECK.
  destruct CERT as [SOURCE BODY OUTER RN RC NC RM CM VALID]; subst source.
  unfold memory_tiled_target,rectangle_described_source; cbn.
  change (projected_region_contract live
    (frontend_counted_loop (rectangle_row d) (rectangle_bound d) (rectangle_described_outer_body d))
    (generated_private_region (@memory_mode_tiled_rectangle_rule mode (described_shape d) VALID
      (described_array d) (rectangle_row d) (rectangle_bound d) (rectangle_column d) (rectangle_inner_bound d)
      (rectangle_inner_body d) (rectangle_described_outer_body d) RN RC NC RM CM BODY OUTER
      live pairs bi bj BI BJ code COMPILE CHECK))).
  apply encoded_private_rule_sound.
Qed.

Definition check_memory_tiled_region live pool bi bj source : CoreAlarmed.Base.imp (option statement) :=
  match Z_lt_dec 0 bi, Z_lt_dec 0 bj, private_counter_pairs pool, describe_memory_tiling source with
  | left _,left _,Some pairs,Some package =>
    let d := tiling_description package in
    match compile_rectangle_mode_tiled (tiling_mode package) (described_shape d) (described_array d) (rectangle_bound d)
      (rectangle_inner_bound d) live pairs bi bj with
    | Some code => BIND valid <- checked_rectangle_mode_tiling (tiling_mode package) (described_shape d) bi bj -;
        pure (if valid then Some (memory_tiled_target package code) else None)
    | None => pure None end
  | _,_,_,_ => pure None end.

Theorem check_memory_tiled_region_sound live pool bi bj source target :
  mayReturn (check_memory_tiled_region live pool bi bj source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_tiled_region.
  destruct (Z_lt_dec 0 bi); [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct (Z_lt_dec 0 bj); [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct (private_counter_pairs pool) as [pairs|]; [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct (describe_memory_tiling source) as [package|]; [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct (compile_rectangle_mode_tiled (tiling_mode package) (described_shape (tiling_description package))
    (described_array (tiling_description package)) (rectangle_bound (tiling_description package))
    (rectangle_inner_bound (tiling_description package)) live pairs bi bj) as [code|] eqn:COMPILE;
    [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  intro CHECK; bind_imp_destruct CHECK valid VALID; apply mayReturn_pure in CHECK.
  destruct valid; [inversion CHECK; subst target|discriminate].
  apply memory_tiled_target_sound with (pairs := pairs) (bi := bi) (bj := bj); assumption.
Qed.

Fixpoint checked_memory_tiled_regions live pool bi bj sources : CoreAlarmed.Base.imp (list (statement * statement)) :=
  match sources with
  | [] => pure []
  | source::rest =>
    BIND candidate <- check_memory_tiled_region live pool bi bj source -;
    BIND table <- checked_memory_tiled_regions live pool bi bj rest -;
    pure (match candidate with Some target => (source,target)::table | None => table end)
  end.
Lemma checked_memory_tiled_regions_sound live pool bi bj sources table :
  mayReturn (checked_memory_tiled_regions live pool bi bj sources) table ->
  Forall (fun pair => projected_region_contract live (fst pair) (snd pair)) table.
Proof.
  revert table; induction sources; intros table CHECK; cbn in CHECK.
  - apply mayReturn_pure in CHECK; subst table; constructor.
  - bind_imp_destruct CHECK candidate CANDIDATE; bind_imp_destruct CHECK rest REST.
    apply mayReturn_pure in CHECK; destruct candidate as [target|]; subst table; [constructor|];
      eauto using check_memory_tiled_region_sound.
Qed.
Fixpoint select_memory_tiled_table table source : option statement :=
  match table with
  | [] => None
  | (original,target)::rest => if statement_eq source original then Some target else select_memory_tiled_table rest source
  end.
Lemma select_memory_tiled_table_sound live table :
  Forall (fun pair => projected_region_contract live (fst pair) (snd pair)) table ->
  forall source target, select_memory_tiled_table table source = Some target -> projected_region_contract live source target.
Proof.
  intro TABLE; induction TABLE as [|[original candidate] rest HEAD TAIL IH]; intros source target; cbn.
  - discriminate.
  - destruct (statement_eq source original) as [EQ|NE]; [subst original|apply IH].
    intro SELECT; inversion SELECT; subst target; exact HEAD.
Qed.

Definition apply_memory_tiled_table pool table program :=
  if private_pool_check (program_temps program) pool then
    PrivateRegion.transform_program pool structured_progress_supported (select_memory_tiled_table table) program
  else program.
Theorem apply_memory_tiled_table_correct pool table program :
  Forall (fun pair => projected_region_contract (program_temps program) (fst pair) (snd pair)) table ->
  forward_simulation (Clight.semantics2 program) (Clight.semantics2 (apply_memory_tiled_table pool table program)).
Proof.
  intro TABLE; unfold apply_memory_tiled_table.
  destruct (private_pool_check (program_temps program) pool) eqn:FRESH.
  - eapply PrivateRegionProof.transform_program_correct2 with (live := program_temps program).
    + exact structured_progress_supported_sound.
    + apply select_memory_tiled_table_sound; exact TABLE.
    + apply program_scope_computed.
    + eapply private_pool_check_sound; exact FRESH.
  - apply forward_simulation_step with (match_states := @eq Clight.state).
    + reflexivity.
    + intros source INIT; exists source; auto.
    + intros; subst; assumption.
    + intros source events next STEP target SAME; subst target; exists next; auto.
Qed.

Definition compile_memory_tiled_regions bi bj (program : Csyntax.program) : CoreAlarmed.Base.imp (res Asm.program) :=
  match SimplExpr.transl_program program with
  | Error errors => pure (Error errors)
  | OK clight => match SimplLocals.transf_program clight with
    | Error errors => pure (Error errors)
    | OK normalized =>
      let live := program_temps normalized in
      let pool := propose_private_names live 8 in
      BIND table <- checked_memory_tiled_regions live pool bi bj (memory_program_candidates normalized) -;
      pure (compile_clight_tail (Compiler.print Compiler.print_Clight
        (apply_memory_tiled_table pool table normalized)))
    end
  end.
Theorem memory_tiled_cstrategy_forward bi bj program target :
  mayReturn (compile_memory_tiled_regions bi bj program) (OK target) ->
  forward_simulation (Cstrategy.semantics program) (Asm.semantics target).
Proof.
  unfold compile_memory_tiled_regions; destruct (SimplExpr.transl_program program) as [clight|errors] eqn:P1.
  2: intro COMPILED; apply mayReturn_pure in COMPILED; discriminate.
  destruct (SimplLocals.transf_program clight) as [normalized|errors] eqn:P2.
  2: intro COMPILED; apply mayReturn_pure in COMPILED; discriminate.
  intro COMPILED; bind_imp_destruct COMPILED table TABLE.
  apply mayReturn_pure in COMPILED; rewrite Compiler.print_identity in COMPILED.
  eapply compose_forward_simulations.
  { eapply SimplExprproof.transl_program_correct; eauto using SimplExprproof.transf_program_match. }
  eapply compose_forward_simulations.
  { eapply SimplLocalsproof.transf_program_correct; eauto using SimplLocalsproof.match_transf_program. }
  eapply compose_forward_simulations.
  { apply apply_memory_tiled_table_correct; eapply checked_memory_tiled_regions_sound; exact TABLE. }
  eapply clight_tail_correct; exact COMPILED.
Qed.
Theorem compile_memory_tiled_regions_correct bi bj program target :
  mayReturn (compile_memory_tiled_regions bi bj program) (OK target) ->
  backward_simulation (Csem.semantics program) (Asm.semantics target).
Proof.
  intro COMPILED.
  apply compose_backward_simulation with (atomic (Cstrategy.semantics program)).
  - eapply sd_traces; eapply Asm.semantics_determinate.
  - apply factor_backward_simulation.
    + apply Cstrategy.strategy_simulation.
    + apply Csem.semantics_single_events.
    + eapply ssr_well_behaved; eapply Cstrategy.semantics_strongly_receptive.
  - apply forward_to_backward_simulation.
    + apply factor_forward_simulation.
      * apply memory_tiled_cstrategy_forward with (bi := bi) (bj := bj); exact COMPILED.
      * eapply sd_traces; eapply Asm.semantics_determinate.
    + apply atomic_receptive; apply Cstrategy.semantics_strongly_receptive.
    + apply Asm.semantics_determinate.
Qed.
Print Assumptions compile_memory_tiled_regions_correct.
