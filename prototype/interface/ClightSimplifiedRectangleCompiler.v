From compcert.common Require Import Errors Smallstep.
From compcert.cfrontend Require Import Csem.
From compcert.x86 Require Import Asm.
From GuardInterface Require Import ClightLoadedMatrixSyntax ClightLoadedRectangleCompiler ClightProbeTree ClightSharedProjectedCompiler.
Set Implicit Arguments.

Definition choose_simplified_rectangle live pool source :=
  match choose_loaded_rectangle live pool source with
  | Some rule => Some (simplified_projected_rule rule)
  | None => None end.
Definition compile_simplified_rectangles := compile_shared_projected choose_simplified_rectangle loaded_nested_supported 2.
Theorem compile_simplified_rectangles_correct p target : compile_simplified_rectangles p = OK target ->
  backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof. apply compile_shared_projected_correct, loaded_nested_supported_sound. Qed.
Print Assumptions choose_simplified_rectangle.
Print Assumptions compile_simplified_rectangles_correct.
