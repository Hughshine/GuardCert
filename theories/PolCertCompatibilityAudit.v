From Stdlib Require Import List ZArith.
From compcert.common Require Import Memory.
From compcert.cfrontend Require Import Ctypes.
From polcert.src Require Import CTy CState CInstr.
From polcert.polygen Require Import Loop.
Set Implicit Arguments.

(** The locked upstream predicate universally quantifies the block and type
    whose lookup must succeed. Its two distinct-block instances contradict
    functionality of the lookup. This audit does not change upstream source. *)
Theorem legacy_valid_uninhabited id ty state : CState.valid id ty state -> False.
Proof.
  destruct state as [[ge locals] memory]; unfold CState.valid; intro VALID.
  destruct (VALID 1%positive type_int32s) as [FIRST _].
  destruct (VALID 2%positive type_int32s) as [SECOND _].
  congruence.
Qed.

Module CompatibilityAudit (Names : C_INSTR_NAMES).
Module I := CInstr Names.
Module L := Loop I.
Theorem legacy_compat_requires_empty_variables variables state :
  I.Compat variables state -> variables = nil.
Proof.
  intro COMPAT; destruct variables; [reflexivity |].
  inversion COMPAT; subst.
  exfalso; destruct state as [[ge locals] memory]; unfold I.State.valid in H1.
  destruct (H1 1%positive type_int32s) as [FIRST _].
  destruct (H1 2%positive type_int32s) as [SECOND _].
  congruence.
Qed.

Theorem legacy_wrapped_loop_requires_empty_variables code context variables first final :
  L.semantics (code, context, variables) first final -> variables = nil.
Proof.
  intro RUN; inversion RUN; subst.
  match goal with EQ : (_, _, _) = (_, _, _) |- _ => inversion EQ; subst end.
  eapply legacy_compat_requires_empty_variables; eassumption.
Qed.
Print Assumptions legacy_wrapped_loop_requires_empty_variables.
End CompatibilityAudit.
Print Assumptions legacy_valid_uninhabited.
