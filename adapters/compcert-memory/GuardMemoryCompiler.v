From Stdlib Require Import List Bool.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST Errors Smallstep.
From compcert.cfrontend Require Import Clight Csyntax Csem.
From Guard Require Import AbstractGuard ClightCondition ClightPureExpr ClightDecisionRule
  ClightSyntaxEquality ClightRegionRule ClightRegionRewrite ClightStraightLine ClightSharedRegion
  ClightRectangularStore ClightRectangularLoops ClightRectangularGuard ClightRectangularRegion
  ClightRectangularSelector ClightRectangularUpdateSelector ClightRectangularRowSelector
  ClightFrontendLoopProtocol ClightNoWrap ClightSignedCancel ClightStructuredProgress
  AdaptiveRegionCompiler.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryClightRectangles GuardMemoryValidatedRectangles.
Import CoreAlarmed.
Import ListNotations.
Import Clight.
Set Implicit Arguments.

Record memory_rectangle_certificate source mode d := MemoryRectangleCertificate {
  memory_rectangle_source : source = rectangle_described_source d;
  memory_rectangle_body : flatten_region (rectangle_inner_body d) =
    [mode_statement mode (described_shape d) (described_array d) (rectangle_row d) (rectangle_column d)];
  memory_rectangle_outer : flatten_region (rectangle_described_outer_body d) =
    [rectangle_reset (rectangle_column d);
      frontend_counted_loop (rectangle_column d) (rectangle_inner_bound d) (rectangle_inner_body d)];
  memory_rectangle_rn : rectangle_row d <> rectangle_bound d;
  memory_rectangle_rc : rectangle_row d <> rectangle_column d;
  memory_rectangle_nc : rectangle_bound d <> rectangle_column d;
  memory_rectangle_rm : rectangle_row d <> rectangle_inner_bound d;
  memory_rectangle_cm : rectangle_column d <> rectangle_inner_bound d;
  memory_rectangle_layout : rectangle_layout_valid (described_shape d)
}.
Definition check_memory_rectangle source mode d : option (memory_rectangle_certificate source mode d).
Proof.
  destruct (statement_eq source (rectangle_described_source d)) as [SOURCE|]; [|exact None].
  destruct (list_eq_dec statement_eq (flatten_region (rectangle_inner_body d))
    [mode_statement mode (described_shape d) (described_array d) (rectangle_row d) (rectangle_column d)])
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
  exact (Some (@MemoryRectangleCertificate source mode d SOURCE BODY OUTER RN RC NC RM CM
    (@rectangle_layout_check_sound (described_shape d) LAYOUT))).
Defined.

Record memory_rectangle_package source := MemoryRectanglePackage {
  package_mode : rectangle_memory_mode;
  package_description : rectangle_description;
  package_syntax : memory_rectangle_certificate source package_mode package_description
}.
Definition try_memory_rectangle mode propose source : option (memory_rectangle_package source) :=
  match propose source with
  | Some d => match check_memory_rectangle source mode d with
    | Some CERT => Some (@MemoryRectanglePackage source mode d CERT) | None => None end
  | None => None end.
Definition describe_memory_rectangle source :=
  match try_memory_rectangle WriteOnly propose_rectangle_description source with
  | Some package => Some package
  | None => match try_memory_rectangle OwnCellUpdate propose_rectangle_update_description source with
    | Some package => Some package
    | None => try_memory_rectangle RowPrefixUpdate propose_rectangle_row_update_description source end
  end.

Definition memory_rectangle_target source (package : memory_rectangle_package source) :=
  let d := package_description package in
  shared_guarded_statement (rectangle_guard_tree (described_shape d)
    (rectangle_row d) (rectangle_bound d) (rectangle_inner_bound d))
    (rectangle_interchanged (rectangle_row d) (rectangle_bound d) (rectangle_column d)
      (rectangle_inner_bound d) (mode_statement (package_mode package) (described_shape d)
        (described_array d) (rectangle_row d) (rectangle_column d))) source.

Theorem memory_rectangle_target_sound source (package : memory_rectangle_package source) :
  mayReturn (checked_rectangle_dependences (package_mode package) (described_shape (package_description package))) true ->
  region_contract source (memory_rectangle_target package).
Proof.
  destruct package as [mode d CERT]; cbn; intro DEPENDENCES.
  destruct CERT as [SOURCE BODY OUTER RN RC NC RM CM VALID]; subst source.
  unfold rectangle_described_source, memory_rectangle_target; cbn.
  change (region_contract (frontend_counted_loop (rectangle_row d) (rectangle_bound d) (rectangle_described_outer_body d))
    (shared_generated_region (@memory_validated_rectangle_rule mode (described_shape d) VALID
      (described_array d) (rectangle_row d) (rectangle_bound d) (rectangle_column d) (rectangle_inner_bound d)
      (rectangle_inner_body d) (rectangle_described_outer_body d) RN RC NC RM CM BODY OUTER DEPENDENCES))).
  apply shared_encoded_region_rule_sound.
Qed.

Definition check_memory_region source : CoreAlarmed.Base.imp (option Clight.statement) :=
  match describe_memory_rectangle source with
  | Some package =>
    BIND valid <- checked_rectangle_dependences (package_mode package)
      (described_shape (package_description package)) -;
    pure (if valid then Some (memory_rectangle_target package) else None)
  | None => pure None end.
Theorem check_memory_region_sound source target :
  mayReturn (check_memory_region source) (Some target) -> region_contract source target.
Proof.
  unfold check_memory_region; destruct (describe_memory_rectangle source) as [package|].
  - intro CHECK; bind_imp_destruct CHECK valid VALID.
    apply mayReturn_pure in CHECK; destruct valid; [inversion CHECK; subst target|discriminate].
    apply memory_rectangle_target_sound; exact VALID.
  - intro CHECK; apply mayReturn_pure in CHECK; discriminate.
Qed.

(** A table is ordinary compiler data. The monadic checker proves every
    accepted entry, after which the existing whole-program host consumes it. *)
Fixpoint checked_memory_regions sources : CoreAlarmed.Base.imp (list (Clight.statement * Clight.statement)) :=
  match sources with
  | [] => pure []
  | source :: rest =>
    BIND candidate <- check_memory_region source -;
    BIND table <- checked_memory_regions rest -;
    pure (match candidate with Some target => (source,target)::table | None => table end)
  end.
Lemma checked_memory_regions_sound sources table :
  mayReturn (checked_memory_regions sources) table ->
  Forall (fun pair => region_contract (fst pair) (snd pair)) table.
Proof.
  revert table; induction sources; intros table CHECK; cbn in CHECK.
  - apply mayReturn_pure in CHECK; subst table; constructor.
  - bind_imp_destruct CHECK candidate CANDIDATE; bind_imp_destruct CHECK rest REST.
    apply mayReturn_pure in CHECK; destruct candidate as [target|]; subst table; [constructor|];
      eauto using check_memory_region_sound.
Qed.
Fixpoint select_memory_table table source : option Clight.statement :=
  match table with
  | [] => select_progress_regions source
  | (original,target)::rest => if statement_eq source original then Some target else select_memory_table rest source
  end.
Lemma select_memory_table_sound table :
  Forall (fun pair => region_contract (fst pair) (snd pair)) table ->
  forall source target, select_memory_table table source = Some target -> region_contract source target.
Proof.
  intro TABLE; induction TABLE as [|[original candidate] rest HEAD TAIL IH]; intros source target; cbn.
  - apply select_progress_regions_sound.
  - destruct (statement_eq source original) as [EQ|NE]; [subst original|apply IH].
    intro SELECT; inversion SELECT; subst target; exact HEAD.
Qed.

Fixpoint memory_statement_candidates (source : Clight.statement) : list Clight.statement :=
  source :: match source with
  | Ssequence first second | Sifthenelse _ first second | Sloop first second =>
      memory_statement_candidates first ++ memory_statement_candidates second
  | Sswitch _ cases => memory_case_candidates cases
  | Slabel _ body => memory_statement_candidates body
  | _ => [] end
with memory_case_candidates (cases : Clight.labeled_statements) : list Clight.statement :=
  match cases with
  | LSnil => []
  | LScons _ body rest => memory_statement_candidates body ++ memory_case_candidates rest end.
Definition memory_program_candidates (program : Clight.program) :=
  flat_map (fun definition => match snd definition with
    | Gfun (Ctypes.Internal f) => memory_statement_candidates (fn_body f)
    | _ => [] end) (Ctypes.prog_defs program).

Definition compile_memory_regions (program : Csyntax.program) : CoreAlarmed.Base.imp (res Asm.program) :=
  match compcert.cfrontend.SimplExpr.transl_program program with
  | Error errors => pure (Error errors)
  | OK clight => match compcert.cfrontend.SimplLocals.transf_program clight with
    | Error errors => pure (Error errors)
    | OK normalized =>
      BIND table <- checked_memory_regions (memory_program_candidates normalized) -;
      pure (compile_with_adaptive_regions structured_progress_supported select_no_wrap
        select_signed_memory_rewrites (select_memory_table table) program)
    end
  end.
Theorem compile_memory_regions_correct program target :
  mayReturn (compile_memory_regions program) (OK target) ->
  backward_simulation (Csem.semantics program) (Asm.semantics target).
Proof.
  unfold compile_memory_regions; destruct (compcert.cfrontend.SimplExpr.transl_program program) as [clight|errors].
  - destruct (compcert.cfrontend.SimplLocals.transf_program clight) as [normalized|errors].
    2: { intro COMPILED; apply mayReturn_pure in COMPILED; discriminate. }
    intro COMPILED; bind_imp_destruct COMPILED table TABLE.
    apply mayReturn_pure in COMPILED.
    eapply compile_with_adaptive_regions_correct; eauto using structured_progress_supported_sound,
      select_no_wrap_sound, select_signed_memory_rewrites_sound.
    apply select_memory_table_sound; eapply checked_memory_regions_sound; exact TABLE.
  - intro COMPILED; apply mayReturn_pure in COMPILED; discriminate.
Qed.
Print Assumptions compile_memory_regions_correct.
