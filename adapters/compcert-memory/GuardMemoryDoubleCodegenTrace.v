From Stdlib Require Import List String.
From polcert.lib Require Import Misc ImpureAlarmConfig.
From Vpl Require Import Impure Debugging.
From GuardMemory Require Import GuardMemoryDoublePolyhedral GuardMemoryDoubleTiledPhaseTrace.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope string_scope.

(** Observe the existing code generator without changing a transformation,
    projection, simplification, cleanup, or certificate check. *)
Definition traced_double_lex_codegen d n pis :=
  BIND polyloop <- double_phase_stage "codegen-ast"
    (fun _ => DoubleAssignmentPrepare.CodeGen.ASTGen.generate_loop_many d n pis) -;
  BIND simplified <- double_phase_stage "codegen-simplify"
    (fun _ => DoubleAssignmentPrepare.CodeGen.PolyLoopSimplifier.polyloop_simplify
      polyloop (n - d)%nat nil) -;
  double_phase_stage "codegen-loop"
    (fun _ => DoubleAssignmentPrepare.CodeGen.LoopGen.polyloop_to_loop
      (n - d)%nat simplified).

Lemma traced_double_lex_codegen_exact d n pis :
  traced_double_lex_codegen d n pis =
  DoubleAssignmentPrepare.CodeGen.complete_generate_lex_many d n pis.
Proof. unfold traced_double_lex_codegen, double_phase_stage, trace; reflexivity. Qed.

Definition traced_double_codegen (pol : DoubleAssignmentIRs.PolyLang.t) :=
  let '(pis, context, variables) := pol in
  let n := Nat.max (List.length variables) (DoubleAssignmentIRs.PolyLang.pprog_current_dim pol) in
  let k := list_max (map (fun pi => List.length pi.(DoubleAssignmentIRs.PolyLang.pi_schedule)) pis) in
  let eliminated := double_phase_stage "codegen-eliminate-schedule"
    (fun _ => DoubleAssignmentIRs.PolyLang.elim_schedule k (List.length context) pis) in
  BIND loop <- traced_double_lex_codegen (n + k - List.length context)%nat (n + k)%nat eliminated -;
  pure (loop, context, variables).

Lemma traced_double_codegen_exact pol :
  traced_double_codegen pol = DoubleAssignmentPrepare.CodeGen.codegen pol.
Proof.
  destruct pol as [[pis context] variables].
  unfold traced_double_codegen, DoubleAssignmentPrepare.CodeGen.codegen,
    DoubleAssignmentPrepare.CodeGen.complete_generate_many,
    traced_double_lex_codegen, DoubleAssignmentPrepare.CodeGen.complete_generate_lex_many,
    double_phase_stage, trace; reflexivity.
Qed.

Definition traced_double_prepared_codegen (pol : DoubleAssignmentIRs.PolyLang.t) :=
  let prepared := double_phase_stage "codegen-prepare"
    (fun _ => DoubleAssignmentPrepare.prepare_codegen pol) in
  BIND loop <- traced_double_codegen prepared -;
  pure (double_phase_stage "codegen-cleanup"
    (fun _ => DoubleAssignmentPrepare.Cleanup.cleanup loop)).

Theorem traced_double_prepared_codegen_exact pol :
  traced_double_prepared_codegen pol = DoubleAssignmentPrepare.prepared_codegen pol.
Proof.
  unfold traced_double_prepared_codegen, DoubleAssignmentPrepare.prepared_codegen,
    DoubleAssignmentPrepare.prepared_codegen_raw, double_phase_stage, trace.
  rewrite traced_double_codegen_exact; reflexivity.
Qed.

Print Assumptions traced_double_lex_codegen_exact.
Print Assumptions traced_double_codegen_exact.
Print Assumptions traced_double_prepared_codegen_exact.
