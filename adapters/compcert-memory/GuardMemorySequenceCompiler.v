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
  GuardMemoryArrayFamilyBackend GuardMemorySequenceTiledClight.
Import CoreAlarmed ListNotations PrivateRegion.
Import Clight.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint propose_array_family_shapes row bound column inner_bound stores : option (list rectangle_shape) :=
  match stores with
  | [] => Some []
  | store::rest =>
    match propose_rectangle_description (frontend_counted_loop row bound
      (rectangle_outer_body column inner_bound store)),
      propose_array_family_shapes row bound column inner_bound rest with
    | Some description,Some shapes => Some (described_shape description::shapes)
    | _,_ => None end
  end.
Definition propose_array_family source : option (rectangle_description * list rectangle_shape) :=
  match propose_frontend_shape source with
  | Some (row,bound,outer_body) => match flatten_region outer_body with
    | [Sset column _;inner_loop] => match propose_frontend_shape inner_loop with
      | Some (_,inner_bound,inner_body) => match flatten_region inner_body with
        | store::rest =>
          match propose_rectangle_description (frontend_counted_loop row bound
            (rectangle_outer_body column inner_bound store)),
            propose_array_family_shapes row bound column inner_bound (store::rest) with
          | Some d,Some shapes => Some
            (RectangleDescription (described_shape d) (described_array d) row bound column inner_bound
              inner_body outer_body,shapes)
          | _,_ => None end
        | [] => None end
      | None => None end
    | _ => None end
  | None => None end.
Record array_family_certificate source d shapes := ArrayFamilyCertificate {
  family_source : source = rectangle_described_source d;
  family_body : flatten_region (rectangle_inner_body d) =
    map (fun shape => rect_store shape (described_array d) (rectangle_row d) (rectangle_column d)) shapes;
  family_outer : flatten_region (rectangle_described_outer_body d) =
    [rectangle_reset (rectangle_column d);
      frontend_counted_loop (rectangle_column d) (rectangle_inner_bound d) (rectangle_inner_body d)];
  family_rn : rectangle_row d <> rectangle_bound d;
  family_rc : rectangle_row d <> rectangle_column d;
  family_nc : rectangle_bound d <> rectangle_column d;
  family_rm : rectangle_row d <> rectangle_inner_bound d;
  family_cm : rectangle_column d <> rectangle_inner_bound d;
  family_layout : rectangle_layout_valid (described_shape d);
  family_layouts : Forall (same_array_layout (described_shape d)) shapes;
  family_nonempty : shapes <> []
}.
Definition check_array_family source d shapes : option (array_family_certificate source d shapes).
Proof.
  destruct (statement_eq source (rectangle_described_source d)) as [SOURCE|]; [|exact None].
  destruct (list_eq_dec statement_eq (flatten_region (rectangle_inner_body d))
    (map (fun shape => rect_store shape (described_array d) (rectangle_row d) (rectangle_column d)) shapes))
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
  destruct (forallb (same_array_layout_check (described_shape d)) shapes) eqn:LAYOUTS; [|exact None].
  assert (ALL : Forall (same_array_layout (described_shape d)) shapes).
  { apply Forall_forall; intros shape MEMBER; apply same_array_layout_check_sound.
    eapply forallb_forall; [exact LAYOUTS|exact MEMBER]. }
  destruct shapes as [|shape shapes]; [exact None|].
  exact (Some (@ArrayFamilyCertificate source d (shape::shapes) SOURCE BODY OUTER RN RC NC RM CM
    (@rectangle_layout_check_sound (described_shape d) LAYOUT) ALL ltac:(discriminate))).
Defined.
Record memory_sequence_package source := MemorySequencePackage {
  sequence_description : rectangle_description;
  sequence_shapes : list rectangle_shape;
  sequence_syntax : array_family_certificate source sequence_description sequence_shapes
}.
Definition describe_memory_sequence source : option (memory_sequence_package source) :=
  match propose_array_family source with
  | Some (d,shapes) => match check_array_family source d shapes with
    | Some CERT => Some (@MemorySequencePackage source d shapes CERT) | None => None end
  | None => None end.
Definition memory_sequence_target source (package : memory_sequence_package source) code :=
  let d := sequence_description package in
  shared_guarded_statement (rectangle_guard_tree (described_shape d)
    (rectangle_row d) (rectangle_bound d) (rectangle_inner_bound d))
    (rectangle_tiled_candidate code (rectangle_row d) (rectangle_bound d)
      (rectangle_column d) (rectangle_inner_bound d)) source.

Theorem memory_sequence_target_sound source (package : memory_sequence_package source) live pairs bi bj code :
  0 < bi -> 0 < bj ->
  compile_array_family_tiled (described_shape (sequence_description package)) (sequence_shapes package)
    (described_array (sequence_description package)) (rectangle_bound (sequence_description package))
    (rectangle_inner_bound (sequence_description package)) live pairs bi bj = Some code ->
  mayReturn (checked_array_family_tiling (described_shape (sequence_description package)) (sequence_shapes package) bi bj) true ->
  projected_region_contract live source (memory_sequence_target package code).
Proof.
  destruct package as [d shapes CERT]; cbn; intros BI BJ COMPILE CHECK.
  destruct CERT as [SOURCE BODY OUTER RN RC NC RM CM VALID LAYOUTS NONEMPTY]; subst source.
  unfold memory_sequence_target,rectangle_described_source; cbn.
  change (projected_region_contract live
    (frontend_counted_loop (rectangle_row d) (rectangle_bound d) (rectangle_described_outer_body d))
    (generated_private_region (@memory_tiled_array_family_rule (described_shape d) VALID shapes LAYOUTS NONEMPTY
      (described_array d) (rectangle_row d) (rectangle_bound d) (rectangle_column d) (rectangle_inner_bound d)
      (rectangle_inner_body d) (rectangle_described_outer_body d) RN RC NC RM CM BODY OUTER
      live pairs bi bj BI BJ code COMPILE CHECK))).
  apply encoded_private_rule_sound.
Qed.

Definition check_memory_sequence_region live pool bi bj source : CoreAlarmed.Base.imp (option statement) :=
  match Z_lt_dec 0 bi, Z_lt_dec 0 bj, private_counter_pairs pool, describe_memory_sequence source with
  | left _,left _,Some pairs,Some package =>
    let d := sequence_description package in
    match compile_array_family_tiled (described_shape d) (sequence_shapes package) (described_array d) (rectangle_bound d)
      (rectangle_inner_bound d) live pairs bi bj with
    | Some code => BIND valid <- checked_array_family_tiling (described_shape d) (sequence_shapes package) bi bj -;
        pure (if valid then Some (memory_sequence_target package code) else None)
    | None => pure None end
  | _,_,_,_ => pure None end.

Theorem check_memory_sequence_region_sound live pool bi bj source target :
  mayReturn (check_memory_sequence_region live pool bi bj source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_sequence_region.
  destruct (Z_lt_dec 0 bi); [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct (Z_lt_dec 0 bj); [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct (private_counter_pairs pool) as [pairs|]; [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct (describe_memory_sequence source) as [package|]; [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct (compile_array_family_tiled (described_shape (sequence_description package)) (sequence_shapes package)
    (described_array (sequence_description package)) (rectangle_bound (sequence_description package))
    (rectangle_inner_bound (sequence_description package)) live pairs bi bj) as [code|] eqn:COMPILE;
    [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  intro CHECK; bind_imp_destruct CHECK valid VALID; apply mayReturn_pure in CHECK.
  destruct valid; [inversion CHECK; subst target|discriminate].
  apply memory_sequence_target_sound with (pairs := pairs) (bi := bi) (bj := bj); assumption.
Qed.

Fixpoint checked_memory_sequence_regions live pool bi bj sources : CoreAlarmed.Base.imp (list (statement * statement)) :=
  match sources with
  | [] => pure []
  | source::rest =>
    BIND candidate <- check_memory_sequence_region live pool bi bj source -;
    BIND table <- checked_memory_sequence_regions live pool bi bj rest -;
    pure (match candidate with Some target => (source,target)::table | None => table end)
  end.
Lemma checked_memory_sequence_regions_sound live pool bi bj sources table :
  mayReturn (checked_memory_sequence_regions live pool bi bj sources) table ->
  Forall (fun pair => projected_region_contract live (fst pair) (snd pair)) table.
Proof.
  revert table; induction sources; intros table CHECK; cbn in CHECK.
  - apply mayReturn_pure in CHECK; subst table; constructor.
  - bind_imp_destruct CHECK candidate CANDIDATE; bind_imp_destruct CHECK rest REST.
    apply mayReturn_pure in CHECK; destruct candidate as [target|]; subst table; [constructor|];
      eauto using check_memory_sequence_region_sound.
Qed.
Definition compile_memory_sequence_regions bi bj (program : Csyntax.program) : CoreAlarmed.Base.imp (res Asm.program) :=
  match SimplExpr.transl_program program with
  | Error errors => pure (Error errors)
  | OK clight => match SimplLocals.transf_program clight with
    | Error errors => pure (Error errors)
    | OK normalized =>
      let live := program_temps normalized in
      let pool := propose_private_names live 8 in
      BIND table <- checked_memory_sequence_regions live pool bi bj (memory_program_candidates normalized) -;
      pure (compile_clight_tail (Compiler.print Compiler.print_Clight
        (apply_memory_tiled_table pool table normalized)))
    end
  end.
Theorem memory_sequence_cstrategy_forward bi bj program target :
  mayReturn (compile_memory_sequence_regions bi bj program) (OK target) ->
  forward_simulation (Cstrategy.semantics program) (Asm.semantics target).
Proof.
  unfold compile_memory_sequence_regions; destruct (SimplExpr.transl_program program) as [clight|errors] eqn:P1.
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
  { apply apply_memory_tiled_table_correct; eapply checked_memory_sequence_regions_sound; exact TABLE. }
  eapply clight_tail_correct; exact COMPILED.
Qed.
Theorem compile_memory_sequence_regions_correct bi bj program target :
  mayReturn (compile_memory_sequence_regions bi bj program) (OK target) ->
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
      * apply memory_sequence_cstrategy_forward with (bi := bi) (bj := bj); exact COMPILED.
      * eapply sd_traces; eapply Asm.semantics_determinate.
    + apply atomic_receptive; apply Cstrategy.semantics_strongly_receptive.
    + apply Asm.semantics_determinate.
Qed.
Print Assumptions compile_memory_sequence_regions_correct.
