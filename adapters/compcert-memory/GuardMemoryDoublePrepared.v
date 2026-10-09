From Stdlib Require Import List Bool ZArith String.
From polcert.src Require Import Base OpenScop PolyLang.
From polcert.polygen Require Import Result.
From polcert.lib Require Import ImpureAlarmConfig Misc.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryValueInstr GuardMemoryDoubleValue
  GuardMemoryDoubleAssignment GuardMemoryDoublePolyhedral.
From GuardInterface Require Import GuardMemoryPreparedPipeline.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.
Module DP := DoubleAssignmentIRs.PolyLang.

(** Scheduling consumes access relations. The importer retains the original
    typed instruction; the textual body is not a new execution semantics. *)
Fixpoint export_double_value names reads expression : option ArrayExpr :=
  match expression with
  | DoubleBits _ => None
  | DoubleRead index => match nth_error reads index with
    | Some access => match export_access names access with
      | Some access => Some (ArrAccessAtom access) | None => None end
    | None => None end
  | DoubleBinary operation first second =>
    match export_double_value names reads first, export_double_value names reads second with
    | Some first, Some second => Some (match operation with
      | DoubleAdd => ArrAdd first second | DoubleSub => ArrMinus first second
      | DoubleMul => ArrMulti first second | DoubleDiv => ArrDiv first second end)
    | _, _ => None end
  | DoubleNegate child => match export_double_value names reads child with
    | Some child => Some (ArrMinus (ArrAtom (AInt 0)) child) | None => None end
  end.
Definition export_double_instruction names (instruction : DoubleAssignmentInstr.t) :=
  match export_access names (value_instruction_write instruction),
    export_double_value names (value_instruction_reads instruction) (value_instruction_code instruction) with
  | Some write, Some value => Some (ArrAssign write value) | _, _ => None end.

Import DP.
Local Open Scope nat_scope.
Definition export_double_statement (pi : PolyInstr) varctxt global_dim : option Statement :=
  let normalized := remove_zero_schedule_dims pi.(pi_schedule) in
  let '(core, tail) := split_trailing_const_schedule normalized in
  let schedule_dim := Nat.max global_dim (List.length core) in
  let domain_rows := dedup_domain_rows pi.(pi_poly) in
  let domain_dim := list_max (map (fun row : list Z * Z => List.length (fst row)) domain_rows) in
  let params := List.length varctxt in
  let iters := domain_dim - params in
  let padded := repeat (constant_affine_function (params+iters) 0%Z) (schedule_dim-List.length core) ++ core in
  let rows := source_like_sctt_rows padded tail (params+iters) in
  let parameter_names := map parameter_name varctxt in
  let iterator_names := map iterator_name (seq 0 pi.(pi_depth)) in
  let arguments := unwrap_option (map (export_affine (map AfVar (parameter_names++iterator_names))) pi.(pi_transformation)) in
  match arguments with
  | None => None
  | Some arguments => match export_double_instruction arguments pi.(pi_instr) with
    | None => None
    | Some body => Some {|
      domain := {| rel_type := DomTy; meta := {| row_nb := List.length domain_rows;
        col_nb := iters+params+2; out_dim_nb := iters; in_dim_nb := 0; local_dim_nb := 0; param_nb := params |};
        constrs := map (fun row => listzzs_to_domain_constr row params iters) domain_rows |};
      scattering := {| rel_type := ScttTy; meta := {| row_nb := List.length rows;
        col_nb := List.length rows+iters+params+2; out_dim_nb := List.length rows;
        in_dim_nb := iters; local_dim_nb := 0; param_nb := params |};
        constrs := affine_rows_to_sctt_constrs rows params iters (List.length rows) |};
      access := map (fun access => access_to_openscop
        (DoubleAssignmentValidator.compose_access_function_at domain_dim access pi.(pi_access_transformation))
        WriteTy params iters) pi.(pi_waccess) ++
        map (fun access => access_to_openscop
        (DoubleAssignmentValidator.compose_access_function_at domain_dim access pi.(pi_access_transformation))
        ReadTy params iters) pi.(pi_raccess);
      stmt_exts_opt := Some [StmtBody iterator_names body] |}
    end
  end.
Definition export_double_model (source : DP.t) : option OpenScop :=
  let '(instructions, parameters, variables) := source in
  let dimension := list_max (map (fun pi =>
    let '(core, _) := split_trailing_const_schedule (remove_zero_schedule_dims pi.(pi_schedule)) in
    List.length core) instructions) in
  match unwrap_option (map (fun pi => export_double_statement pi parameters dimension) instructions) with
  | None => None
  | Some statements => Some {|
    context := {| lang := "C"; param_domain := {| rel_type := CtxtTy;
      meta := {| row_nb := 0; col_nb := List.length parameters+2; out_dim_nb := 0;
        in_dim_nb := 0; local_dim_nb := 0; param_nb := List.length parameters |}; constrs := [] |};
      params := Some (map parameter_name parameters) |};
    statements := statements;
    glb_exts := [ArrayExt (map (fun variable =>
      (DoubleAssignmentInstr.ident_to_openscop_ident (fst variable), array_name (fst variable))) variables)] |}
  end.

(** The external callback supplies data. Validation and prepared codegen are
    the actual DoubleAssignmentIRs operations, with the original instructions. *)
Definition checked_double_prepared_phase (schedule : OpenScop -> result OpenScop) (source : DP.t) :=
  match export_double_model source with
  | None => pure None
  | Some before => match schedule before with
    | Err _ => pure None
    | Okk after => match DP.from_openscop_like_source source after with
      | Err _ => pure None
      | Okk proposed => checked_double_schedule_codegen source proposed
      end
    end
  end.
Theorem checked_double_prepared_phase_correct schedule source generated initial final :
  mayReturn (checked_double_prepared_phase schedule source) (Some generated) ->
  DoubleAssignmentIRs.Loop.semantics generated initial final ->
  DP.instance_list_semantics source initial final.
Proof.
  unfold checked_double_prepared_phase.
  destruct (export_double_model source) as [before|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (schedule before) as [after|message]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (DP.from_openscop_like_source source after) as [proposed|message];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  apply checked_double_schedule_codegen_correct.
Qed.
Definition checked_double_prepared_loop schedule (source : DoubleAssignmentIRs.Loop.t) :=
  match DoubleAssignmentExtractor.extractor source with
  | Err _ => pure None
  | Okk extracted => checked_double_prepared_phase schedule extracted
  end.
Theorem checked_double_prepared_loop_correct schedule source generated initial final :
  mayReturn (checked_double_prepared_loop schedule source) (Some generated) ->
  DoubleAssignmentIRs.Loop.semantics generated initial final ->
  DoubleAssignmentIRs.Loop.semantics source initial final.
Proof.
  unfold checked_double_prepared_loop.
  destruct (DoubleAssignmentExtractor.extractor source) as [model|message] eqn:EXTRACT;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intros RUN EXEC.
  pose proof (@checked_double_prepared_phase_correct schedule model generated initial final RUN EXEC) as MODEL.
  destruct (DoubleAssignmentExtractor.extractor_correct _ _ _ _ EXTRACT MODEL) as [result [SOURCE SAME]].
  unfold DoubleAssignmentIRs.State.eq, DoubleAssignmentInstr.State.eq in SAME; subst result; exact SOURCE.
Qed.

Print Assumptions checked_double_prepared_phase_correct.
Print Assumptions checked_double_prepared_loop_correct.
