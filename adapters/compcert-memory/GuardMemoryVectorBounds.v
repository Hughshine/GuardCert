From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Integers Coqlib.
From compcert.common Require Import AST.
From Guard Require Import ClightCondition ClightPureExpr ClightGuard ClightCountedLoop ClightRectangularGuard ClightRedundantSet ClightNoWrap.
From GuardMemory Require Import GuardMemoryRegistryGuard.
From GuardMemory Require Import GuardMemoryTripleGuard GuardMemoryRecursiveGuard.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint memory_vector_bounds_accept (caps : list Z) (bounds : list ident) s :=
  match caps,bounds with
  | [],[] => true
  | cap::rest,bound::tail => register_range_flag bound cap s && memory_vector_bounds_accept rest tail s
  | _,_ => false end.
Fixpoint memory_vector_bounds_domain (caps : list Z) (bounds : list ident) s : Prop :=
  match caps,bounds with
  | cap::rest,bound::tail => register_domain bound s /\
      (register_range_flag bound cap s = true -> memory_vector_bounds_domain rest tail s)
  | _,_ => True end.
Fixpoint memory_vector_bounds_tree (caps : list Z) (bounds : list ident) terminal :=
  match caps,bounds with
  | [],[] => terminal
  | cap::rest,bound::tail => decision_bind (register_range_tree bound cap)
      (memory_vector_bounds_tree rest tail terminal) (Decision false)
  | _,_ => Decision false end.

Theorem memory_vector_bounds_exact caps bounds terminal s accepted :
  memory_vector_bounds_domain caps bounds s ->
  (memory_vector_bounds_accept caps bounds s = true -> forall flag, decision_run s terminal flag <-> flag = accepted) ->
  forall flag, decision_run s (memory_vector_bounds_tree caps bounds terminal) flag <->
    flag = memory_vector_bounds_accept caps bounds s && accepted.
Proof.
  revert bounds; induction caps as [|cap caps IH]; intros [|bound bounds] DOMAIN TERMINAL flag;
    cbn [memory_vector_bounds_domain memory_vector_bounds_accept memory_vector_bounds_tree] in *.
  - apply TERMINAL; reflexivity.
  - split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor].
  - split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor].
  - destruct DOMAIN as [BOUND REST]; rewrite <-andb_assoc.
    apply memory_guard_gate_exact; [apply memory_triple_range_exact; exact BOUND|].
    intro RANGE; apply IH; [apply REST; exact RANGE|].
    intro ALL; apply TERMINAL; rewrite RANGE,ALL; reflexivity.
Qed.

Theorem memory_vector_bounds_sound caps bounds s :
  Forall signed_range caps -> memory_vector_bounds_domain caps bounds s ->
  memory_vector_bounds_accept caps bounds s = true ->
  Forall2 (fun cap bound => register_range bound cap s) caps bounds.
Proof.
  intro CAPS; revert bounds; induction CAPS as [|cap caps CAP CAPS IH]; intros [|bound bounds] DOMAIN ACCEPT;
    cbn in *; try discriminate; constructor.
  - destruct DOMAIN as [BOUND REST]; apply andb_true_iff in ACCEPT as [RANGE ALL].
    apply register_range_sound; assumption.
  - destruct DOMAIN as [BOUND REST]; apply andb_true_iff in ACCEPT as [RANGE ALL].
    apply IH; [apply REST; exact RANGE|exact ALL].
Qed.

Lemma memory_register_range_monotone bound lower upper s :
  signed_range lower -> signed_range upper -> lower <= upper ->
  register_range_flag bound lower s = true -> register_range_flag bound upper s = true.
Proof.
  intros LOWER UPPER ORDER RANGE; unfold register_range_flag in *; apply andb_true_iff in RANGE as [POSITIVE MAX].
  apply andb_true_iff; split; [exact POSITIVE|].
  unfold register_at_most,Int.lt in *; rewrite Int.signed_repr in MAX by exact LOWER.
  rewrite Int.signed_repr by exact UPPER.
  destruct (zlt lower (Int.signed (temp_word bound (entry_temps s)))); cbn in MAX; [discriminate|].
  destruct (zlt upper (Int.signed (temp_word bound (entry_temps s)))); cbn; [lia|reflexivity].
Qed.

Theorem memory_vector_bounds_domain_from_uniform caps bounds upper s :
  length caps = length bounds -> Forall (fun cap => signed_range cap /\ cap <= upper) caps ->
  signed_range upper -> memory_recursive_bounds_domain upper bounds s ->
  memory_vector_bounds_domain caps bounds s.
Proof.
  intro LENGTH; revert bounds LENGTH; induction caps as [|cap caps IH]; intros [|bound bounds] LENGTH CAPS UPPER DOMAIN;
    cbn in LENGTH; try discriminate; cbn; [exact I|].
  inversion CAPS as [|cc cs [SIGNED ORDER] REST]; subst.
  destruct DOMAIN as [BOUND TAIL]; split; [exact BOUND|]; intro RANGE.
  eapply IH; [lia|exact REST|exact UPPER|].
  apply TAIL; eapply memory_register_range_monotone; eassumption.
Qed.
Print Assumptions memory_vector_bounds_exact.
Print Assumptions memory_vector_bounds_sound.
Print Assumptions memory_register_range_monotone.
Print Assumptions memory_vector_bounds_domain_from_uniform.
