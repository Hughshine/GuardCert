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
  ClightFrontendLoopProtocol ClightFrontendRegion ClightStraightLine ClightSharedRegion ClightSyntaxEquality.
From GuardMemory Require Import GuardMemoryClightRectangles GuardMemoryCompiler GuardMemoryTiledClight GuardMemoryTiledCompiler
  GuardMemoryCutClight GuardMemoryCutTiledClight.
Import CoreAlarmed ListNotations PrivateRegion.
Import Clight.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** This parser proposes coefficients only. The certificate independently
    checks the full typed expression, loop protocol, body, and frame. *)
Fixpoint propose_cut_coefficients row column expression : option (Z * Z) :=
  match expression with
  | Etempvar id _ => if peq id row then Some (1,0) else if peq id column then Some (0,1) else None
  | Ebinop Cop.Oadd first second _ =>
    match propose_cut_coefficients row column first, propose_cut_coefficients row column second with
    | Some (a,b),Some (c,d) => Some (a+c,b+d) | _,_ => None end
  | Ebinop Cop.Omul constant operand _ =>
    match propose_rectangle_constant constant,propose_cut_coefficients row column operand with
    | Some k,Some (a,b) => Some (k*a,k*b) | _,_ => None end
  | Econst_int value _ => if Integers.Int.eq value Integers.Int.zero then Some (0,0) else None
  | _ => None end.
Definition propose_memory_cut source : option (rectangle_description * Z * Z * Z * expr) :=
  match propose_frontend_shape source with
  | Some (row,bound,outer_body) => match flatten_region outer_body with
    | [Sset column _;inner_loop] => match propose_frontend_shape inner_loop with
      | Some (_,inner_bound,inner_body) => match flatten_region inner_body with
        | [Sifthenelse (Ebinop Cop.Ole lhs limit ty as condition) payload Sskip] =>
          match propose_rectangle_description (frontend_counted_loop row bound
            (rectangle_outer_body column inner_bound payload)),
            propose_cut_coefficients row column lhs,propose_rectangle_constant limit with
          | Some d,Some (a,b),Some c => Some
            (RectangleDescription (described_shape d) (described_array d) row bound column inner_bound
              inner_body outer_body,a,b,c,condition)
          | _,_,_ => None end
        | _ => None end
      | None => None end
    | _ => None end
  | None => None end.
Record memory_cut_certificate source d a b c condition := MemoryCutCertificate {
  cut_source : source = rectangle_described_source d;
  cut_body : flatten_region (rectangle_inner_body d) =
    [memory_cut_statement (described_shape d) (described_array d) (rectangle_row d) (rectangle_column d) condition];
  cut_outer : flatten_region (rectangle_described_outer_body d) =
    [rectangle_reset (rectangle_column d);
      frontend_counted_loop (rectangle_column d) (rectangle_inner_bound d) (rectangle_inner_body d)];
  cut_rn : rectangle_row d <> rectangle_bound d;
  cut_rc : rectangle_row d <> rectangle_column d;
  cut_nc : rectangle_bound d <> rectangle_column d;
  cut_rm : rectangle_row d <> rectangle_inner_bound d;
  cut_cm : rectangle_column d <> rectangle_inner_bound d;
  cut_layout : rectangle_layout_valid (described_shape d);
  cut_limit : 0 <= c;
  cut_encoding : compile_memory_cut_condition (described_shape d) (rectangle_row d) (rectangle_column d) a b c = Some condition
}.
Definition check_memory_cut source d a b c condition : option (memory_cut_certificate source d a b c condition).
Proof.
  destruct (statement_eq source (rectangle_described_source d)) as [SOURCE|]; [|exact None].
  destruct (list_eq_dec statement_eq (flatten_region (rectangle_inner_body d))
    [memory_cut_statement (described_shape d) (described_array d) (rectangle_row d) (rectangle_column d) condition])
    as [BODY|]; [|exact None].
  destruct (list_eq_dec statement_eq (flatten_region (rectangle_described_outer_body d))
    [rectangle_reset (rectangle_column d);
      frontend_counted_loop (rectangle_column d) (rectangle_inner_bound d) (rectangle_inner_body d)])
    as [OUTER|]; [|exact None].
  destruct (peq (rectangle_row d) (rectangle_bound d)) as [|RN]; [exact None|].
  destruct (peq (rectangle_row d) (rectangle_column d)) as [|RC]; [exact None|].
  destruct (peq (rectangle_bound d) (rectangle_column d)) as [|NC]; [exact None|].
  destruct (peq (rectangle_row d) (rectangle_inner_bound d)) as [|RM]; [exact None|].
  destruct (peq (rectangle_column d) (rectangle_inner_bound d)) as [|CM]; [exact None|].
  destruct (rectangle_layout_check (described_shape d)) eqn:LAYOUT; [|exact None].
  destruct (Z_le_dec 0 c) as [LIMIT|]; [|exact None].
  destruct (compile_memory_cut_condition (described_shape d) (rectangle_row d) (rectangle_column d) a b c)
    as [computed|] eqn:ENCODE; [|exact None].
  destruct (expression_eq computed condition) as [EQ|]; [subst computed|exact None].
  exact (Some (@MemoryCutCertificate source d a b c condition SOURCE BODY OUTER RN RC NC RM CM
    (@rectangle_layout_check_sound (described_shape d) LAYOUT) LIMIT ENCODE)).
Defined.
Record memory_cut_package source := MemoryCutPackage {
  cut_description : rectangle_description;
  cut_a : Z; cut_b : Z; cut_c : Z; cut_condition : expr;
  cut_syntax : memory_cut_certificate source cut_description cut_a cut_b cut_c cut_condition
}.
Definition describe_memory_cut source : option (memory_cut_package source) :=
  match propose_memory_cut source with
  | Some (d,a,b,c,condition) => match check_memory_cut source d a b c condition with
    | Some CERT => Some (@MemoryCutPackage source d a b c condition CERT) | None => None end
  | None => None end.

Definition memory_cut_target source (package : memory_cut_package source) code :=
  let d := cut_description package in
  shared_guarded_statement (rectangle_guard_tree (described_shape d)
    (rectangle_row d) (rectangle_bound d) (rectangle_inner_bound d))
    (rectangle_tiled_candidate code (rectangle_row d) (rectangle_bound d)
      (rectangle_column d) (rectangle_inner_bound d)) source.

Theorem memory_cut_target_sound source (package : memory_cut_package source) live pairs bi bj code :
  0 < bi -> 0 < bj ->
  compile_cut_tiled (described_shape (cut_description package))
    (described_array (cut_description package)) (rectangle_bound (cut_description package))
    (rectangle_inner_bound (cut_description package)) live pairs bi bj (cut_a package) (cut_b package) (cut_c package) = Some code ->
  mayReturn (checked_cut_tiling (described_shape (cut_description package)) bi bj (cut_a package) (cut_b package) (cut_c package)) true ->
  projected_region_contract live source (memory_cut_target package code).
Proof.
  destruct package as [d a b c condition CERT]; cbn; intros BI BJ COMPILE CHECK.
  destruct CERT as [SOURCE BODY OUTER RN RC NC RM CM VALID LIMIT ENCODE]; subst source.
  unfold memory_cut_target,rectangle_described_source; cbn.
  change (projected_region_contract live
    (frontend_counted_loop (rectangle_row d) (rectangle_bound d) (rectangle_described_outer_body d))
    (generated_private_region (@memory_cut_tiled_rule (described_shape d) VALID a b c LIMIT condition
      (described_array d) (rectangle_row d) (rectangle_bound d) (rectangle_column d) (rectangle_inner_bound d) ENCODE
      (rectangle_inner_body d) (rectangle_described_outer_body d) RN RC NC RM CM BODY OUTER
      live pairs bi bj BI BJ code COMPILE CHECK))).
  apply encoded_private_rule_sound.
Qed.

Definition check_memory_cut_region live pool bi bj source : CoreAlarmed.Base.imp (option statement) :=
  match Z_lt_dec 0 bi, Z_lt_dec 0 bj, private_counter_pairs pool, describe_memory_cut source with
  | left _,left _,Some pairs,Some package =>
    let d := cut_description package in
    match compile_cut_tiled (described_shape d) (described_array d) (rectangle_bound d)
      (rectangle_inner_bound d) live pairs bi bj (cut_a package) (cut_b package) (cut_c package) with
    | Some code => BIND valid <- checked_cut_tiling (described_shape d) bi bj (cut_a package) (cut_b package) (cut_c package) -;
        pure (if valid then Some (memory_cut_target package code) else None)
    | None => pure None end
  | _,_,_,_ => pure None end.

Theorem check_memory_cut_region_sound live pool bi bj source target :
  mayReturn (check_memory_cut_region live pool bi bj source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_cut_region.
  destruct (Z_lt_dec 0 bi); [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct (Z_lt_dec 0 bj); [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct (private_counter_pairs pool) as [pairs|]; [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct (describe_memory_cut source) as [package|]; [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct (compile_cut_tiled (described_shape (cut_description package))
    (described_array (cut_description package)) (rectangle_bound (cut_description package))
    (rectangle_inner_bound (cut_description package)) live pairs bi bj (cut_a package) (cut_b package) (cut_c package)) as [code|] eqn:COMPILE;
    [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  intro CHECK; bind_imp_destruct CHECK valid VALID; apply mayReturn_pure in CHECK.
  destruct valid; [inversion CHECK; subst target|discriminate].
  apply memory_cut_target_sound with (pairs := pairs) (bi := bi) (bj := bj); assumption.
Qed.

Fixpoint checked_memory_cut_regions live pool bi bj sources : CoreAlarmed.Base.imp (list (statement * statement)) :=
  match sources with
  | [] => pure []
  | source::rest =>
    BIND candidate <- check_memory_cut_region live pool bi bj source -;
    BIND table <- checked_memory_cut_regions live pool bi bj rest -;
    pure (match candidate with Some target => (source,target)::table | None => table end)
  end.
Lemma checked_memory_cut_regions_sound live pool bi bj sources table :
  mayReturn (checked_memory_cut_regions live pool bi bj sources) table ->
  Forall (fun pair => projected_region_contract live (fst pair) (snd pair)) table.
Proof.
  revert table; induction sources; intros table CHECK; cbn in CHECK.
  - apply mayReturn_pure in CHECK; subst table; constructor.
  - bind_imp_destruct CHECK candidate CANDIDATE; bind_imp_destruct CHECK rest REST.
    apply mayReturn_pure in CHECK; destruct candidate as [target|]; subst table; [constructor|];
      eauto using check_memory_cut_region_sound.
Qed.
Fixpoint select_memory_cut_table table source : option statement :=
  match table with
  | [] => None
  | (original,target)::rest => if statement_eq source original then Some target else select_memory_cut_table rest source
  end.
Lemma select_memory_cut_table_sound live table :
  Forall (fun pair => projected_region_contract live (fst pair) (snd pair)) table ->
  forall source target, select_memory_cut_table table source = Some target -> projected_region_contract live source target.
Proof.
  intro TABLE; induction TABLE as [|[original candidate] rest HEAD TAIL IH]; intros source target; cbn.
  - discriminate.
  - destruct (statement_eq source original) as [EQ|NE]; [subst original|apply IH].
    intro SELECT; inversion SELECT; subst target; exact HEAD.
Qed.

Definition apply_memory_cut_table pool table program :=
  if private_pool_check (program_temps program) pool then
    PrivateRegion.transform_program pool structured_progress_supported (select_memory_cut_table table) program
  else program.
Theorem apply_memory_cut_table_correct pool table program :
  Forall (fun pair => projected_region_contract (program_temps program) (fst pair) (snd pair)) table ->
  forward_simulation (Clight.semantics2 program) (Clight.semantics2 (apply_memory_cut_table pool table program)).
Proof.
  intro TABLE; unfold apply_memory_cut_table.
  destruct (private_pool_check (program_temps program) pool) eqn:FRESH.
  - eapply PrivateRegionProof.transform_program_correct2 with (live := program_temps program).
    + exact structured_progress_supported_sound.
    + apply select_memory_cut_table_sound; exact TABLE.
    + apply program_scope_computed.
    + eapply private_pool_check_sound; exact FRESH.
  - apply forward_simulation_step with (match_states := @eq Clight.state).
    + reflexivity.
    + intros source INIT; exists source; auto.
    + intros; subst; assumption.
    + intros source events next STEP target SAME; subst target; exists next; auto.
Qed.

Definition compile_memory_cut_regions bi bj (program : Csyntax.program) : CoreAlarmed.Base.imp (res Asm.program) :=
  match SimplExpr.transl_program program with
  | Error errors => pure (Error errors)
  | OK clight => match SimplLocals.transf_program clight with
    | Error errors => pure (Error errors)
    | OK normalized =>
      let live := program_temps normalized in
      let pool := propose_private_names live 8 in
      BIND table <- checked_memory_cut_regions live pool bi bj (memory_program_candidates normalized) -;
      pure (compile_clight_tail (Compiler.print Compiler.print_Clight
        (apply_memory_cut_table pool table normalized)))
    end
  end.
Theorem memory_cut_cstrategy_forward bi bj program target :
  mayReturn (compile_memory_cut_regions bi bj program) (OK target) ->
  forward_simulation (Cstrategy.semantics program) (Asm.semantics target).
Proof.
  unfold compile_memory_cut_regions; destruct (SimplExpr.transl_program program) as [clight|errors] eqn:P1.
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
  { apply apply_memory_cut_table_correct; eapply checked_memory_cut_regions_sound; exact TABLE. }
  eapply clight_tail_correct; exact COMPILED.
Qed.
Theorem compile_memory_cut_regions_correct bi bj program target :
  mayReturn (compile_memory_cut_regions bi bj program) (OK target) ->
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
      * apply memory_cut_cstrategy_forward with (bi := bi) (bj := bj); exact COMPILED.
      * eapply sd_traces; eapply Asm.semantics_determinate.
    + apply atomic_receptive; apply Cstrategy.semantics_strongly_receptive.
    + apply Asm.semantics_determinate.
Qed.
Print Assumptions compile_memory_cut_regions_correct.
