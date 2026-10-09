From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.polygen Require Import InstrTy Loop.
From Guard Require Import PolCertLoopGuard PolCertAffineClight
  PolCertQuotientParameter ClightTempFrame.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Check and execute an actual nonnegative division into a fresh private
    temporary. The result extends the typed model environment and establishes
    an affine relation usable by the final candidate checker. *)
Module PolCertQuotientCaptureFor (I : INSTR) (M : LOOP_MODEL I).
Module L := M.
Module Machine := PolCertAffineClightFor I M.
Module Model := PolCertQuotientParameterFor I M.
Definition compile_capture layout ranges quotient numerator divisor :=
  match Machine.compile_expr layout ranges (L.Div numerator divisor) with
  | Some (code,bound) => Some (Sset quotient code,bound)
  | None => None end.
Theorem quotient_capture_execution layout ranges quotient numerator divisor code bound
  environment temps live fe ge locals memory :
  compile_capture layout ranges quotient numerator divisor=Some (code,bound) ->
  Machine.env_within ranges environment -> Machine.typed_view layout environment temps ->
  ~ In quotient (layout++live) ->
  let value := L.eval_expr environment numerator/divisor in
  let captured := PTree.set quotient (Vint (Int.repr value)) temps in
  exec_stmt fe ge locals temps memory code E0 captured memory Out_normal /\
  Machine.typed_view (quotient::layout) (value::environment) captured /\
  Machine.env_within (bound::ranges) (value::environment) /\
  L.eval_test (value::environment) (Model.quotient_relation numerator divisor)=true /\
  temp_agree (layout++live) temps captured.
Proof.
  unfold compile_capture.
  destruct (Machine.compile_expr layout ranges (L.Div numerator divisor)) as [[expression interval]|]
    eqn:COMPILE; try discriminate.
  intros CODE WITHIN VIEW FRESH; inversion CODE; subst code bound; cbn zeta.
  destruct (@Machine.compile_expr_sound layout ranges (L.Div numerator divisor) expression interval
    environment temps COMPILE WITHIN VIEW) as [TYPE [RANGE [CONTAINS EVAL]]].
  assert (POSITIVE : 0<divisor).
  { unfold Machine.compile_expr in COMPILE.
    destruct (Machine.analyze ranges (L.Div numerator divisor)) as [checked|] eqn:ANAL;
      try discriminate.
    pose proof (@Machine.analyze_sound (L.Div numerator divisor) ranges checked environment ANAL WITHIN)
      as [_ SAFE]; cbn [Machine.affine_safe] in SAFE; tauto. }
  split; [constructor; apply EVAL|].
  split.
  - apply Machine.typed_view_cons; [exact RANGE| |exact VIEW].
    intro MEMBER; apply FRESH, in_or_app; left; exact MEMBER.
  - split; [apply Machine.env_within_cons; assumption|].
    split.
    + apply (proj2 (@Model.quotient_relation_exact numerator divisor environment
        (L.eval_expr environment numerator/divisor) POSITIVE)); reflexivity.
    + apply temp_agree_set; exact FRESH.
Qed.
Lemma quotient_capture_writes layout ranges quotient numerator divisor code bound :
  compile_capture layout ranges quotient numerator divisor=Some (code,bound) ->
  writes_only [quotient] code.
Proof.
  unfold compile_capture.
  destruct (Machine.compile_expr layout ranges (L.Div numerator divisor)) as [[expression interval]|];
    try discriminate.
  intro CODE; inversion CODE; subst; constructor; cbn; auto.
Qed.
End PolCertQuotientCaptureFor.
