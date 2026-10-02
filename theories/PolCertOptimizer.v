From Stdlib Require Import List ZArith.
From Guard Require Import AbstractGuard SemanticFacts.
From GuardPolCert Require Import PolCertLoopProgram.
From polcert.polygen Require Import PolIRs.
From polcert.lib Require Import ImpureAlarmConfig.
From polcert.driver Require Import PolOptCorrect.
From Vpl Require Import Impure.
Set Implicit Arguments.
Local Open Scope impure_scope.

(** This adapter calls the actual verified optimizer, then uses the generic
    condition compiler through the real Loop language. It retains the upstream
    alarm-monad successful-result contract; it does not prove native extraction. *)
Module PolCertOptimizer (P : POLIRS) (Core : POL_OPT_CORE P).
Module Endpoint := PolOptCorrect P Core.
Module Program := PolCertLoopProgramFor P.Instr P.Loop.
Module G := Program.G.
Module L := Program.L.

Definition optimize_version {A} (domain : G.entry -> Prop)
  (property : A -> G.entry -> Prop)
  (atoms : forall a, G.encoded_atom domain (property a)) (condition : formula A)
  (source : L.t) : imp L.t :=
  BIND candidate <- Core.Opt_prepared source -;
  pure (Program.checked_version domain property atoms condition source candidate).

Arguments optimize_version {A} domain property atoms condition source.

Theorem optimize_version_correct {A} (domain : G.entry -> Prop)
  (property : A -> G.entry -> Prop)
  (atoms : forall a, G.encoded_atom domain (property a)) condition source :
  (forall s, Program.admissible source s -> domain s) ->
  forall m result,
  WHEN target <- optimize_version domain property atoms condition source THEN
  L.semantics target m result ->
  exists result', L.semantics source m result' /\ P.State.eq result result'.
Proof.
  intros DOMAIN m result target OPT RUN.
  unfold optimize_version in OPT.
  bind_imp_destruct OPT candidate CANDIDATE.
  apply mayReturn_pure in OPT. subst target.
  eapply Program.checked_version_refines; [exact DOMAIN | | exact RUN].
  intros m0 result0 CAND_RUN.
  exact (Endpoint.Opt_prepared_correct source m0 result0 candidate CANDIDATE CAND_RUN).
Qed.

Goal True. idtac "GUARDCERT_OPT_BASELINE_BEGIN". exact Logic.I. Qed.
Print Assumptions Endpoint.Opt_prepared_correct.
Goal True. idtac "GUARDCERT_OPT_ADAPTER_BEGIN". exact Logic.I. Qed.
Print Assumptions optimize_version_correct.
Goal True. idtac "GUARDCERT_OPT_ASSUMPTIONS_END". exact Logic.I. Qed.

End PolCertOptimizer.
