From Stdlib Require Import List Bool ZArith String Numbers.DecimalString.
From compcert.common Require Import AST.
From polcert.src Require Import Base OpenScop PolyLang PrepareCodegen ExtractorCorrect.
From polcert.polygen Require Import Result.
From polcert.lib Require Import ImpureAlarmConfig Misc.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryPolyhedral.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.
Module MemoryPrepared.
Module PrepareCore := PrepareCodegen GuardMemoryIRs.
Module Extractor := ExtractorCorrect GuardMemoryIRs.
End MemoryPrepared.
Module MP := GuardMemoryIRs.PolyLang.

(** OpenScop is an untrusted scheduling interface. Use legal, distinct C names
    for parameters, iterators and logical arrays; import retains source
    instructions and accesses, and the validator checks the returned schedule. *)
Definition parameter_name identifier := String.append "p_" (GuardMemoryInstr.ident_to_varname identifier).
Definition iterator_name index := String.append "i_" (GuardMemoryInstr.iterator_to_varname index).
Definition array_name identifier := String.append "a_" (GuardMemoryInstr.ident_to_varname identifier).
Fixpoint export_affine_terms names coefficients : option AffineExpr :=
  match coefficients,names with
  | [],_ => Some (AfInt 0)
  | coefficient::rest,name::names => match export_affine_terms names rest with
    | Some tail => Some (AfAdd (AfMulti (AfInt coefficient) name) tail)
    | None => None end
  | _,[] => None end.
Definition export_affine names term :=
  let '(coefficients,bias) := term in
  match export_affine_terms names coefficients with
  | Some expression => Some (AfAdd expression (AfInt bias)) | None => None end.
Fixpoint export_coordinates names coordinates : option (list AffineExpr) :=
  match coordinates with
  | [] => Some []
  | coordinate::rest => match export_affine names coordinate,export_coordinates names rest with
    | Some first,Some tail => Some (first::tail) | _,_ => None end end.
Definition export_access names access :=
  let '(identifier,coordinates) := access in
  match export_coordinates names coordinates with
  | Some coordinates => Some (ArrAccess (array_name identifier) coordinates) | None => None end.
Fixpoint array_of_affine expression : ArrayExpr :=
  match expression with
  | AfInt value => ArrAtom (AInt value)
  | AfVar name => ArrAtom (AVar name)
  | AfAdd first second => ArrAdd (array_of_affine first) (array_of_affine second)
  | AfMinus first second => ArrMinus (array_of_affine first) (array_of_affine second)
  | AfMulti first second => ArrMulti (array_of_affine first) (array_of_affine second)
  | AfDiv first second => ArrDiv (array_of_affine first) (array_of_affine second) end.
Fixpoint export_value names reads expression : option ArrayExpr :=
  match expression with
  | ConstantValue value => Some (ArrAtom (AInt value))
  | ParameterValue index => match nth_error names index with
    | Some expression => Some (array_of_affine expression) | None => None end
  | LoadedValue index => match nth_error reads index with
    | Some access => match export_access names access with
      | Some access => Some (ArrAccessAtom access) | None => None end
    | None => None end
  | AddValue first second => match export_value names reads first,export_value names reads second with
    | Some first,Some second => Some (ArrAdd first second) | _,_ => None end
  | SubValue first second => match export_value names reads first,export_value names reads second with
    | Some first,Some second => Some (ArrMinus first second) | _,_ => None end
  | MulValue first second => match export_value names reads first,export_value names reads second with
    | Some first,Some second => Some (ArrMulti first second) | _,_ => None end end.
Definition export_instruction names instruction :=
  match export_access names (instruction_write instruction),
    export_value names (instruction_reads instruction) (instruction_value instruction) with
  | Some write,Some value => Some (ArrAssign write value) | _,_ => None end.

Import MP.
Local Open Scope nat_scope.
Definition export_memory_statement
    (pi: PolyInstr) (varctxt: list ident) (global_compact_sctt_dim: nat): option Statement :=
  let normalized_sched := remove_zero_schedule_dims pi.(pi_schedule) in
  let '(sched_core_raw, tail_const) := split_trailing_const_schedule normalized_sched in
  let compact_sctt_dim := Nat.max global_compact_sctt_dim (List.length sched_core_raw) in
  let domain_rows := dedup_domain_rows pi.(pi_poly) in
  let domain_dim := list_max (map
    (fun (constr: (list Z * Z)) => let (zs, z) := constr in
      List.length zs) domain_rows) in
  let varctxt_dim := List.length varctxt in
  let iters_dim := domain_dim - varctxt_dim in
  let sched_core :=
    repeat (constant_affine_function (varctxt_dim + iters_dim) 0%Z)
      (compact_sctt_dim - List.length sched_core_raw) ++
    sched_core_raw in
  let rows := source_like_sctt_rows sched_core tail_const (varctxt_dim + iters_dim) in
  let varctxt_varnames := map parameter_name varctxt in
  let iters_varnames := map iterator_name (seq 0 (pi.(pi_depth))) in
  let arguments := unwrap_option (map
    (export_affine (map AfVar (List.app varctxt_varnames iters_varnames)))
    pi.(pi_transformation)) in
  match (match arguments with Some args => export_instruction args pi.(pi_instr)
         | None => None end) with
  | Some arr_stmt =>
    Some {|
      OpenScop.domain := {|
        OpenScop.rel_type := OpenScop.DomTy;
        OpenScop.meta := {|
          OpenScop.row_nb := List.length domain_rows;
          OpenScop.col_nb := iters_dim + varctxt_dim + 2;
          OpenScop.out_dim_nb := iters_dim;
          OpenScop.in_dim_nb := 0;
          OpenScop.local_dim_nb := 0;
          OpenScop.param_nb := varctxt_dim;
        |};
        OpenScop.constrs := map (fun constr => listzzs_to_domain_constr constr varctxt_dim iters_dim) domain_rows;
      |};
      OpenScop.scattering := {|
        OpenScop.rel_type := OpenScop.ScttTy;
        OpenScop.meta := {|
          OpenScop.row_nb := List.length rows;
          OpenScop.col_nb := List.length rows + iters_dim + varctxt_dim + 2;
          OpenScop.out_dim_nb := List.length rows;
          OpenScop.in_dim_nb := iters_dim;
          OpenScop.local_dim_nb := 0;
          OpenScop.param_nb := varctxt_dim;
        |};
        OpenScop.constrs :=
          affine_rows_to_sctt_constrs rows varctxt_dim iters_dim (List.length rows);
      |};
      OpenScop.access :=
        (map (fun access => access_to_openscop
          (GuardMemoryValidator.compose_access_function_at domain_dim access pi.(pi_access_transformation))
          OpenScop.WriteTy varctxt_dim iters_dim) (pi.(pi_waccess))) ++
        (map (fun access => access_to_openscop
          (GuardMemoryValidator.compose_access_function_at domain_dim access pi.(pi_access_transformation))
          OpenScop.ReadTy varctxt_dim iters_dim) (pi.(pi_raccess)));
      OpenScop.stmt_exts_opt :=
      Some ([
        OpenScop.StmtBody (
          iters_varnames
        )
        arr_stmt
      ]);
    |}
  | None => None
  end
  .

Definition export_memory_model (pol: t): option OpenScop :=
  let '(pis, varctxt, vars) := pol in
  let context := {|
    OpenScop.lang := "C";
    OpenScop.param_domain := {|
      OpenScop.rel_type := OpenScop.CtxtTy;
      OpenScop.meta := {|
        OpenScop.row_nb := 0;
        OpenScop.col_nb := List.length (varctxt) + 2;
        OpenScop.out_dim_nb := 0;
        OpenScop.in_dim_nb := 0;
        OpenScop.local_dim_nb := 0;
        OpenScop.param_nb := List.length (varctxt);
      |};
      OpenScop.constrs := nil;
    |};
    OpenScop.params := Some (List.map parameter_name varctxt);
  |} in
  let compact_sctt_dim :=
    list_max (List.map
      (fun pi =>
        let normalized_sched := remove_zero_schedule_dims pi.(pi_schedule) in
        let '(sched_core, _) := split_trailing_const_schedule normalized_sched in
        List.length sched_core)
      pis) in
  let ostatements := unwrap_option (List.map (fun pi => export_memory_statement pi varctxt compact_sctt_dim) pis) in
  let glb_exts := (
      ArrayExt (List.map (fun x => (GuardMemoryInstr.ident_to_openscop_ident (fst x), array_name (fst x))) vars)
  )::nil in 
  match ostatements with
  | Some statements => 
    Some {|
      OpenScop.context := context; 
      OpenScop.statements := statements;
      OpenScop.glb_exts := glb_exts;
    |}
  | None => None
  end
  .


(** Failed export, scheduling or import refuses this optimization. Unlike the
    old disconnected POLIRS instance, the phase runner is an explicit argument.
    It supplies data only; all imports and transitions are checked. *)
Definition checked_memory_prepared_phase (schedule : OpenScop -> result OpenScop)
    (source : MP.t) : Base.imp (option GuardMemoryIRs.Loop.t) :=
  match export_memory_model source with
  | None => pure None
  | Some before => match schedule before with
    | Err _ => pure None
    | Okk after => match MP.from_openscop_like_source source after with
      | Err _ => pure None
      | Okk proposed => BIND valid <- GuardMemoryValidator.validate source proposed -;
        if valid then BIND generated <- MemoryPrepared.PrepareCore.prepared_codegen proposed -;
          pure (Some generated)
        else pure None end end end.

Theorem checked_memory_prepared_phase_correct schedule source generated initial final :
  mayReturn (checked_memory_prepared_phase schedule source) (Some generated) ->
  GuardMemoryIRs.Loop.semantics generated initial final ->
  MP.instance_list_semantics source initial final.
Proof.
  unfold checked_memory_prepared_phase.
  destruct (export_memory_model source) as [before|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (schedule before) as [after|message];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (MP.from_openscop_like_source source after) as [proposed|message];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN valid VALID.
  destruct valid; [|apply mayReturn_pure in RUN; discriminate].
  bind_imp_destruct RUN code CODE; apply mayReturn_pure in RUN; inversion RUN; subst code.
  intro EXEC.
  destruct (GuardMemoryValidator.validate_preserve_wf_pprog _ _ _ VALID eq_refl) as [_ WF].
  apply guarded_memory_validate_refines with (candidate:=proposed); [exact VALID|].
  exact (MemoryPrepared.PrepareCore.prepared_codegen_correct _ _ _ _ CODE WF EXEC).
Qed.

Definition checked_memory_prepared_loop schedule (source : GuardMemoryIRs.Loop.t) :=
  match MemoryPrepared.Extractor.extractor source with
  | Err _ => pure None
  | Okk extracted => checked_memory_prepared_phase schedule extracted end.
Theorem checked_memory_prepared_loop_correct schedule source generated initial final :
  mayReturn (checked_memory_prepared_loop schedule source) (Some generated) ->
  GuardMemoryIRs.Loop.semantics generated initial final ->
  GuardMemoryIRs.Loop.semantics source initial final.
Proof.
  unfold checked_memory_prepared_loop.
  destruct (MemoryPrepared.Extractor.extractor source) as [model|message] eqn:EXTRACT;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intros RUN EXEC.
  pose proof (@checked_memory_prepared_phase_correct schedule model generated initial final RUN EXEC) as MODEL.
  destruct (MemoryPrepared.Extractor.extractor_correct _ _ _ _ EXTRACT MODEL)
    as [result [SOURCE SAME]].
  unfold GuardMemoryIRs.State.eq,GuardMemoryInstr.State.eq in SAME; subst result; exact SOURCE.
Qed.
Print Assumptions checked_memory_prepared_phase_correct.
Print Assumptions checked_memory_prepared_loop_correct.
