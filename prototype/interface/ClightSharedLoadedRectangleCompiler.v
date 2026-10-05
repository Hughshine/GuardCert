From compcert.common Require Import Errors Smallstep.
From compcert.cfrontend Require Import Csem.
From compcert.x86 Require Import Asm.
From GuardInterface Require Import ClightLoadedMatrixSyntax ClightLoadedRectangleCompiler ClightSharedProjectedCompiler.
Set Implicit Arguments.

(** The same user rewrite, condition synthesis and local proof. Only the
    certified lowering adapter changes; one Boolean and one cache are private. *)
Definition compile_shared_loaded_rectangles :=
  compile_shared_projected choose_loaded_rectangle loaded_nested_supported 2.
Theorem compile_shared_loaded_rectangles_correct p target :
  compile_shared_loaded_rectangles p = OK target -> backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof. apply compile_shared_projected_correct, loaded_nested_supported_sound. Qed.
Print Assumptions compile_shared_loaded_rectangles_correct.
