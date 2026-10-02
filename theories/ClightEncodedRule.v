From Stdlib Require Import ZArith.
From Guard Require Import Presumption Synthesis ClightGuard.
From compcert.cfrontend Require Import Clight Cop.

(** The first Clight plugin interface.  Its state view contains temporaries;
    memory guards and state-changing candidates require a richer adapter. *)
Record encoded_branch_rule (source_condition machine_condition : expr) := {
  rule_modulus : Z;
  rule_view : temp_env -> Presumption.state;
  rule_obligation : temp_env -> Prop;
  rule_encoding : Synthesis.presumption_encoding rule_modulus rule_view rule_obligation;
  rule_lowering : forall ge e le m v b,
    eval_expr ge e le m source_condition v ->
    bool_val v (typeof source_condition) m = Some b ->
    exists vg bg,
      eval_expr ge e le m machine_condition vg /\
      bool_val vg (typeof machine_condition) m = Some bg /\
      Synthesis.execute rule_modulus (rule_view le)
        (Synthesis.synthesize (Synthesis.encoded_presumption rule_encoding)) = Some bg;
  rule_local_correct : forall ge e le m v b,
    eval_expr ge e le m source_condition v ->
    bool_val v (typeof source_condition) m = Some b ->
    rule_obligation le -> b = false
}.

Theorem encoded_branch_rule_sound : forall a g,
  encoded_branch_rule a g -> guard_contract a g.
Proof.
  intros a g [modulus view obligation encoding LOWER LOCAL] ge e le m v b EV BV.
  destruct (LOWER ge e le m v b EV BV) as [vg [bg [EG [BG CHECK]]]].
  exists vg, bg. split; [exact EG|]. split; [exact BG|].
  intro ACCEPT. eapply LOCAL; eauto.
  apply (proj1 (@Synthesis.encoded_condition_correct temp_env modulus view
    obligation encoding le bg CHECK)); exact ACCEPT.
Qed.

Print Assumptions encoded_branch_rule_sound.
