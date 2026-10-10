From Stdlib Require Import List Bool.
From polcert.polygen Require Import InstrTy Loop.
From Guard Require Import PolCertLoopGuard PolCertGuardResidualization.
Set Implicit Arguments.

(** Adjacent guards observe the same Loop environment. Instruction effects
    change the model state, but cannot change the cached parameter environment.
    The concrete lowering theorem supplies that separation at the host level. *)
Module PolCertAdjacentGuardsFor (I : INSTR) (M : LOOP_MODEL I).
Module L := M.
Module R := PolCertGuardResidualizationFor I M.
Module IS := I.IterSem.
Definition join_head head tail :=
  match head,tail with
  | L.Guard test body,L.SCons (L.Guard next following) rest=>
    if R.test_eq_dec test next then
      L.SCons (L.Guard test (L.Seq (L.SCons body (L.SCons following L.SNil)))) rest
    else L.SCons head tail
  | _,_=>L.SCons head tail end.
Lemma equal_guards_execution test first second rest env before after :
  L.loop_semantics (L.Seq (L.SCons (L.Guard test first)
    (L.SCons (L.Guard test second) rest))) env before after ->
  L.loop_semantics (L.Seq (L.SCons
    (L.Guard test (L.Seq (L.SCons first (L.SCons second L.SNil)))) rest)) env before after.
Proof.
  intro RUN; inversion RUN; subst.
  match goal with TAIL : L.loop_semantics (L.Seq (L.SCons _ _)) _ _ _ |- _=>inversion TAIL; subst end.
  destruct (L.eval_test env test) eqn:TEST.
  - match goal with FIRST : L.loop_semantics (L.Guard _ _) _ _ _ |- _=>inversion FIRST; subst; clear FIRST end;
      try congruence.
    match goal with SECOND : L.loop_semantics (L.Guard _ _) _ _ _ |- _=>inversion SECOND; subst; clear SECOND end;
      try congruence.
    eapply L.LSeq; [apply L.LGuardTrue; [|exact TEST]|eassumption].
    eapply L.LSeq; [eassumption|eapply L.LSeq; [eassumption|constructor]].
  - repeat match goal with GUARD : L.loop_semantics (L.Guard _ _) _ _ _ |- _=>
      inversion GUARD; subst; clear GUARD end; try congruence.
    eapply L.LSeq; [apply L.LGuardFalse; exact TEST|eassumption].
Qed.
Lemma join_head_execution head tail env before after :
  L.loop_semantics (L.Seq (L.SCons head tail)) env before after ->
  L.loop_semantics (L.Seq (join_head head tail)) env before after.
Proof.
  destruct head; cbn [join_head]; try tauto.
  destruct tail; [tauto|]; destruct s; cbn [join_head]; try tauto.
  destruct (R.test_eq_dec t t0) as [<-|DIFFERENT]; [apply equal_guards_execution|tauto].
Qed.
Fixpoint factor_statement (statement : L.stmt) : L.stmt :=
  match statement with
  | L.Loop lower upper body=>L.Loop lower upper (factor_statement body)
  | L.Guard test body=>L.Guard test (factor_statement body)
  | L.Seq sequence=>L.Seq (factor_sequence sequence)
  | _=>statement end
with factor_sequence (sequence : L.stmt_list) : L.stmt_list :=
  match sequence with L.SNil=>L.SNil
  | L.SCons head tail=>join_head (factor_statement head) (factor_sequence tail) end.
Scheme factoring_stmt_ind := Induction for L.stmt Sort Prop
with factoring_list_ind := Induction for L.stmt_list Sort Prop.
Combined Scheme factoring_ind from factoring_stmt_ind,factoring_list_ind.
Theorem factor_sound :
  (forall statement env before after, L.loop_semantics statement env before after ->
    L.loop_semantics (factor_statement statement) env before after) /\
  (forall sequence env before after, L.loop_semantics (L.Seq sequence) env before after ->
    L.loop_semantics (L.Seq (factor_sequence sequence)) env before after).
Proof.
  apply factoring_ind; intros.
  - cbn [factor_statement]; inversion H0; subst; apply L.LLoop.
    eapply IS.iter_semantics_map with (P:=fun x=>L.loop_semantics s (x::env)); [intros; eapply H; eauto|eassumption].
  - cbn [factor_statement]; assumption.
  - cbn [factor_statement]; eauto.
  - cbn [factor_statement]; inversion H0; subst;
      [apply L.LGuardTrue; [eapply H; eauto|assumption]|apply L.LGuardFalse; assumption].
  - cbn [factor_sequence]; assumption.
  - cbn [factor_sequence]; apply join_head_execution; inversion H1; subst; eapply L.LSeq; [eapply H|eapply H0]; eauto.
Qed.
Corollary factor_execution statement env before after :
  L.loop_semantics statement env before after ->L.loop_semantics (factor_statement statement) env before after.
Proof. apply factor_sound. Qed.
End PolCertAdjacentGuardsFor.
