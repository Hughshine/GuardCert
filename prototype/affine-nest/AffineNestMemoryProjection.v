From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCountedLoop ClightTempFrame ClightLoopSyntax
  ClightFrontendLoopProtocol.
From GuardAffineNest Require Import AffineNestLoopTrace.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Section MEMORY_PROJECTION.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable iterator bound : ident.
Variable body : statement.
Variable protected written : list ident.
Variable original : temp_env.
Hypothesis WRITES : writes_only written body.
Hypothesis PROTECTED : forall identifier, In identifier protected -> ~In identifier written.
Hypothesis ITERATOR_PRIVATE : ~In iterator protected.

(** The source point retains its actual temporary inputs and stable parameter
    snapshot. No fictional memory action or different pointer environment is
    substituted for the real Clight body execution. Instruction-model
    correspondence is a separate adapter obligation. *)
Definition affine_actual_body_point x before after :=
  exists temps final_temps,
    temp_agree protected original temps /\
    temps!iterator=Some(Vint(Int.repr x)) /\
    exec_stmt fe ge locals temps before body E0 final_temps after Out_normal.

Theorem affine_trace_memory_projection count x temps memory after final_memory :
  affine_frontend_trace fe ge locals iterator body count x temps memory after final_memory ->
  temps!iterator=Some(Vint(Int.repr x)) -> temp_agree protected original temps ->
  counted_iterations affine_actual_body_point count x memory final_memory.
Proof.
  intro TRACE; induction TRACE; intros ITERATOR VIEW.
  - constructor.
  - econstructor.
    + exists temps,middle; split; [exact VIEW|split; [exact ITERATOR|exact H]].
    + apply IHTRACE; [apply PTree.gss|].
      eapply temp_agree_trans; [exact VIEW|].
      eapply temp_agree_trans; [|apply temp_agree_set; exact ITERATOR_PRIVATE].
      eapply structured_temp_frame; [exact WRITES|exact PROTECTED|exact H].
Qed.

Theorem affine_frontend_memory_projection :
  iterator<>bound -> normal_statement body=true ->
  ~In iterator written -> ~In bound written ->
  forall upper count x temps memory after final_memory,
  signed_range upper -> upper=x+Z.of_nat count -> signed_range x ->
  temps!iterator=Some(Vint(Int.repr x)) -> temps!bound=Some(Vint(Int.repr upper)) ->
  temp_agree protected original temps ->
  exec_stmt fe ge locals temps memory (frontend_counted_loop iterator bound body)
    E0 after final_memory Out_normal ->
  counted_iterations affine_actual_body_point count x memory final_memory.
Proof.
  intros DISTINCT NORMAL ITERATOR_FRESH BOUND_FRESH upper count x temps memory after final_memory
    UPPER SPAN RANGE ITERATOR BOUND VIEW SOURCE.
  assert (FRAME:forall before initial trace next target,
    exec_stmt fe ge locals before initial body trace next target Out_normal ->
    temp_agree [iterator;bound] before next).
  { intros before initial trace next target RUN.
    eapply structured_temp_frame; [exact WRITES| |exact RUN].
    intros identifier MEMBER; cbn in MEMBER; destruct MEMBER as [SAME|[SAME|BAD]];
      [subst; exact ITERATOR_FRESH|subst; exact BOUND_FRESH|contradiction]. }
  pose proof (@affine_frontend_trace_decode fe ge locals iterator bound body DISTINCT NORMAL FRAME
    upper UPPER count x temps memory after final_memory SPAN RANGE ITERATOR BOUND SOURCE) as TRACE.
  eapply affine_trace_memory_projection; eassumption.
Qed.
End MEMORY_PROJECTION.
Print Assumptions affine_trace_memory_projection.
Print Assumptions affine_frontend_memory_projection.
