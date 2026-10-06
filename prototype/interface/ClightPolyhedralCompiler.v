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
  ClightStructuredProgress ClightStraightLine ClightRectangularSelector ClightRegionProgress GuardCompiler.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryNamedOperations
  GuardMemoryNamedCandidate GuardMemoryNamedCompiler GuardMemoryTiledCompiler GuardMemoryCompiler.
From GuardInterface Require Import ClightPolyhedralPreservation.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition preserving_dispatch_pool (shared : bool) (pool : list (ident * type)) :=
  if shared then match pool with
    | (result,ty)::rest => if type_eq ty type_int32s then Some (result,rest) else None
    | [] => None end
  else Some (1%positive,pool).

Definition choose_named_preserving_lowering live source (package : memory_named_package source) code (shared : bool) result :
  option Clight.statement :=
  if shared then
    if Bool.bool_dec (quiet_statement (named_preserving_branch package code)) true then
      if in_dec peq result (statement_temps (named_preserving_branch package code) ++ statement_temps source ++ live)
      then None else Some (named_preserving_target package code true result)
    else None
  else Some (named_preserving_target package code false result).

Theorem choose_named_preserving_lowering_sound live source (package : memory_named_package source)
  pairs candidate code shared result target :
  compile_named_array_candidate (described_shape (named_description package)) (named_operations package)
    (rectangle_bound (named_description package)) (rectangle_inner_bound (named_description package))
    live pairs candidate = Some code ->
  memory_named_candidate_certificate (described_shape (named_description package)) (named_operations package) candidate ->
  choose_named_preserving_lowering live package code shared result = Some target ->
  PrivateRegion.projected_region_contract live source target.
Proof.
  intros COMPILE CERT; unfold choose_named_preserving_lowering; destruct shared.
  - destruct (Bool.bool_dec (quiet_statement (named_preserving_branch package code)) true) as [QUIET|]; [|discriminate].
    destruct (in_dec peq result (statement_temps (named_preserving_branch package code) ++ statement_temps source ++ live))
      as [|FRESH]; [discriminate|].
    intro SAME; injection SAME as SAME; subst target.
    exact (@named_preserving_target_sound source package live pairs candidate code true result
      COMPILE CERT (fun _ => conj QUIET FRESH)).
  - intro SAME; injection SAME as SAME; subst target; apply (@named_preserving_target_sound source package live pairs candidate code false result);
      [exact COMPILE|exact CERT|discriminate].
Qed.

Definition check_preserving_polyhedral_region shared live pool
  (propose : preserving_polyhedral_proposer) source : CoreAlarmed.Base.imp (option Clight.statement) :=
  match preserving_dispatch_pool shared pool, describe_memory_named source with
  | Some (result,private), Some package =>
    match private_counter_pairs private,
      propose (map named_operation_instruction (named_operations package)) with
    | Some pairs, Some proposal =>
      BIND candidate <- checked_named_preserving_candidate package proposal -;
      pure (match candidate with
        | Some loop =>
          let d := named_description package in
          match compile_named_array_candidate (described_shape d) (named_operations package)
            (rectangle_bound d) (rectangle_inner_bound d) live pairs loop with
          | Some code => choose_named_preserving_lowering live package code shared result
          | None => None end
        | None => None end)
    | _, _ => pure None end
  | _, _ => pure None end.

Theorem check_preserving_polyhedral_region_sound shared live pool propose source target :
  mayReturn (check_preserving_polyhedral_region shared live pool propose source) (Some target) ->
  PrivateRegion.projected_region_contract live source target.
Proof.
  unfold check_preserving_polyhedral_region.
  destruct (preserving_dispatch_pool shared pool) as [[result private]|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (describe_memory_named source) as [package|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (private_counter_pairs private) as [pairs|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (propose (map named_operation_instruction (named_operations package))) as [proposal|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN candidate CANDIDATE; apply mayReturn_pure in RUN.
  destruct candidate as [loop|]; [|discriminate].
  destruct (compile_named_array_candidate (described_shape (named_description package)) (named_operations package)
    (rectangle_bound (named_description package)) (rectangle_inner_bound (named_description package))
    live pairs loop) as [code|] eqn:COMPILE; [|discriminate].
  eapply choose_named_preserving_lowering_sound; [exact COMPILE| |exact RUN].
  eapply checked_named_preserving_candidate_sound; exact CANDIDATE.
Qed.

Fixpoint checked_preserving_polyhedral_regions shared live pool propose sources :
  CoreAlarmed.Base.imp (list (Clight.statement * Clight.statement)) :=
  match sources with
  | [] => pure []
  | source::rest =>
    BIND candidate <- check_preserving_polyhedral_region shared live pool propose source -;
    BIND table <- checked_preserving_polyhedral_regions shared live pool propose rest -;
    pure (match candidate with Some target => (source,target)::table | None => table end)
  end.
Theorem checked_preserving_polyhedral_regions_sound shared live pool propose sources table :
  mayReturn (checked_preserving_polyhedral_regions shared live pool propose sources) table ->
  Forall (fun pair => PrivateRegion.projected_region_contract live (fst pair) (snd pair)) table.
Proof.
  revert table; induction sources as [|source rest IH]; intros table RUN; cbn in RUN.
  - apply mayReturn_pure in RUN; subst table; constructor.
  - bind_imp_destruct RUN candidate CANDIDATE; bind_imp_destruct RUN rest_table TAIL.
    apply mayReturn_pure in RUN; destruct candidate as [target|]; subst table;
      [constructor; [eapply check_preserving_polyhedral_region_sound; exact CANDIDATE|]|];
      apply IH; exact TAIL.
Qed.

(** The table records actual checked AST replacements. The established private
    region traversal supplies scopes, legal source progress and continuations. *)
Definition apply_preserving_polyhedral_table pool table (p : Clight.program) :=
  transform_private_program structured_progress_supported
    (fun _ _ => select_memory_tiled_table table) pool p.
Theorem apply_preserving_polyhedral_table_correct pool table p :
  Forall (fun pair => PrivateRegion.projected_region_contract (program_temps p) (fst pair) (snd pair)) table ->
  forward_simulation (Clight.semantics2 p) (Clight.semantics2 (apply_preserving_polyhedral_table pool table p)).
Proof.
  apply apply_memory_tiled_table_correct.
Qed.

Definition compile_preserving_polyhedral shared propose private_count (program : Csyntax.program) :
  CoreAlarmed.Base.imp (res Asm.program) :=
  match SimplExpr.transl_program program with
  | Error errors => pure (Error errors)
  | OK clight => match SimplLocals.transf_program clight with
    | Error errors => pure (Error errors)
    | OK normalized =>
      let live := program_temps normalized in
      let pool := propose_private_names live private_count in
      BIND table <- checked_preserving_polyhedral_regions shared live pool propose
        (memory_program_candidates normalized) -;
      pure (compile_clight_tail (Compiler.print Compiler.print_Clight
        (apply_preserving_polyhedral_table pool table normalized)))
    end
  end.

Theorem preserving_polyhedral_cstrategy_forward shared propose private_count program target :
  mayReturn (compile_preserving_polyhedral shared propose private_count program) (OK target) ->
  forward_simulation (Cstrategy.semantics program) (Asm.semantics target).
Proof.
  unfold compile_preserving_polyhedral.
  destruct (SimplExpr.transl_program program) as [clight|errors] eqn:P1.
  2: intro RUN; apply mayReturn_pure in RUN; discriminate.
  destruct (SimplLocals.transf_program clight) as [normalized|errors] eqn:P2.
  2: intro RUN; apply mayReturn_pure in RUN; discriminate.
  intro RUN; bind_imp_destruct RUN table TABLE.
  apply mayReturn_pure in RUN; rewrite Compiler.print_identity in RUN.
  eapply compose_forward_simulations.
  { eapply SimplExprproof.transl_program_correct; eauto using SimplExprproof.transf_program_match. }
  eapply compose_forward_simulations.
  { eapply SimplLocalsproof.transf_program_correct; eauto using SimplLocalsproof.match_transf_program. }
  eapply compose_forward_simulations.
  { apply apply_preserving_polyhedral_table_correct;
      eapply checked_preserving_polyhedral_regions_sound; exact TABLE. }
  eapply clight_tail_correct; exact RUN.
Qed.

Theorem compile_preserving_polyhedral_correct shared propose private_count program target :
  mayReturn (compile_preserving_polyhedral shared propose private_count program) (OK target) ->
  backward_simulation (Csem.semantics program) (Asm.semantics target).
Proof.
  intro RUN; apply compose_backward_simulation with (atomic (Cstrategy.semantics program)).
  - eapply sd_traces; eapply Asm.semantics_determinate.
  - apply factor_backward_simulation.
    + apply Cstrategy.strategy_simulation.
    + apply Csem.semantics_single_events.
    + eapply ssr_well_behaved; eapply Cstrategy.semantics_strongly_receptive.
  - apply forward_to_backward_simulation.
    + apply factor_forward_simulation.
      * eapply preserving_polyhedral_cstrategy_forward; exact RUN.
      * eapply sd_traces; eapply Asm.semantics_determinate.
    + apply atomic_receptive; apply Cstrategy.semantics_strongly_receptive.
    + apply Asm.semantics_determinate.
Qed.

Print Assumptions choose_named_preserving_lowering_sound.
Print Assumptions check_preserving_polyhedral_region_sound.
Print Assumptions checked_preserving_polyhedral_regions_sound.
Print Assumptions apply_preserving_polyhedral_table_correct.
Print Assumptions compile_preserving_polyhedral_correct.
