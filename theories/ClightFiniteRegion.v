From Stdlib Require Import Bool List Arith Lia.
From compcert.lib Require Import Coqlib Maps.
From compcert.common Require Import AST Values Memory Events Smallstep.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightGuard.
Import ListNotations.
Local Open Scope nat_scope.

(** A first region class with a syntactic bound on silent source steps.
    The surrounding function can contain arbitrary Clight control flow. *)
Fixpoint finite_statement (s : statement) : bool :=
  match s with
  | Sskip | Sassign _ _ | Sset _ _ => true
  | Ssequence l r | Sifthenelse _ l r => finite_statement l && finite_statement r
  | _ => false
  end.

Fixpoint statement_weight (s : statement) : nat :=
  match s with
  | Sskip => 0
  | Ssequence l r => 2 + statement_weight l + statement_weight r
  | Sifthenelse _ l r => 1 + Nat.max (statement_weight l) (statement_weight r)
  | _ => 1
  end.

Fixpoint continuation_weight (k : cont) : nat :=
  match k with
  | Kseq s k => 1 + statement_weight s + continuation_weight k
  | Kloop1 _ _ k | Kloop2 _ _ k | Kswitch k | Kcall _ _ _ _ k =>
      continuation_weight k
  | Kstop => 0
  end.

Definition state_weight (s : state) : nat :=
  match s with
  | State _ s k _ _ _ => statement_weight s + continuation_weight k
  | _ => 0
  end.

Lemma statement_weight_zero s : statement_weight s = 0 -> s = Sskip.
Proof. destruct s; simpl; intro ZERO; try reflexivity; lia. Qed.

Fixpoint region_cont (stack : list statement) (k : cont) : cont :=
  match stack with [] => k | s :: rest => Kseq s (region_cont rest k) end.

Section REGION.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable e : env.

Inductive fragment_step : statement -> list statement -> temp_env -> mem ->
  statement -> list statement -> temp_env -> mem -> Prop :=
| fs_assign : forall l r stack le m b ofs bf v2 v m',
    eval_lvalue ge e le m l b ofs bf -> eval_expr ge e le m r v2 ->
    sem_cast v2 (typeof r) (typeof l) m = Some v ->
    assign_loc ge (typeof l) m b ofs bf v m' ->
    fragment_step (Sassign l r) stack le m Sskip stack le m'
| fs_set : forall id a stack le m v,
    eval_expr ge e le m a v ->
    fragment_step (Sset id a) stack le m Sskip stack (PTree.set id v le) m
| fs_seq : forall l r stack le m,
    fragment_step (Ssequence l r) stack le m l (r :: stack) le m
| fs_pop : forall s stack le m,
    fragment_step Sskip (s :: stack) le m s stack le m
| fs_if : forall a l r stack le m v b,
    eval_expr ge e le m a v -> bool_val v (typeof a) m = Some b ->
    fragment_step (Sifthenelse a l r) stack le m
      (if b then l else r) stack le m.

Inductive tail_execution : list statement -> temp_env -> mem -> temp_env -> mem -> Prop :=
| tail_nil : forall le m, tail_execution [] le m le m
| tail_cons : forall s stack le m le1 m1 le' m',
    exec_stmt fe ge e le m s E0 le1 m1 Out_normal ->
    tail_execution stack le1 m1 le' m' -> tail_execution (s :: stack) le m le' m'.

Definition resumed_execution s stack le m le' m' : Prop :=
  exists le1 m1, exec_stmt fe ge e le m s E0 le1 m1 Out_normal /\
    tail_execution stack le1 m1 le' m'.

Lemma fragment_step_prepend : forall s stack le m s' stack' le1 m1,
  fragment_step s stack le m s' stack' le1 m1 -> forall le' m',
  resumed_execution s' stack' le1 m1 le' m' -> resumed_execution s stack le m le' m'.
Proof.
  intros s stack le m s' stack' le1 m1 STEP le' m' [le2 [m2 [RUN TAIL]]].
  inversion STEP; subst.
  - inversion RUN; subst. eexists; eexists; split; [econstructor; eauto | exact TAIL].
  - inversion RUN; subst. eexists; eexists; split; [econstructor; eauto | exact TAIL].
  - inversion TAIL; subst. eexists; eexists; split.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); eauto.
    + assumption.
  - exists le1, m1; split; [constructor |]. econstructor; eauto.
  - eexists; eexists; split; [eapply exec_Sifthenelse; eauto | exact TAIL].
Qed.

Lemma fragment_step_finite : forall s stack le m s' stack' le' m',
  fragment_step s stack le m s' stack' le' m' ->
  finite_statement s = true -> Forall (fun s => finite_statement s = true) stack ->
  finite_statement s' = true /\ Forall (fun s => finite_statement s = true) stack'.
Proof.
  intros s stack le m s' stack' le' m' STEP FIN STACK; inversion STEP; subst;
    simpl in FIN.
  - split; auto.
  - split; auto.
  - apply andb_true_iff in FIN as [L R]. split; auto.
  - inversion STACK; subst; auto.
  - apply andb_true_iff in FIN as [L R]. destruct b; auto.
Qed.

Lemma fragment_step_decreases : forall s stack le m s' stack' le' m',
  fragment_step s stack le m s' stack' le' m' -> forall f k,
  state_weight (State f s' (region_cont stack' k) e le' m') <
  state_weight (State f s (region_cont stack k) e le m).
Proof.
  intros s stack le m s' stack' le' m' STEP f k; inversion STEP; subst; simpl;
    try lia.
  destruct b; simpl; pose proof (Nat.le_max_l (statement_weight l) (statement_weight r));
    pose proof (Nat.le_max_r (statement_weight l) (statement_weight r)); lia.
Qed.

Lemma fragment_step_from_ambient : forall f s stack k le m t next,
  finite_statement s = true -> Forall (fun s => finite_statement s = true) stack ->
  (s <> Sskip \/ stack <> []) ->
  step ge (fe ge) (State f s (region_cont stack k) e le m) t next ->
  exists s' stack' le' m', t = E0 /\
    next = State f s' (region_cont stack' k) e le' m' /\
    fragment_step s stack le m s' stack' le' m'.
Proof.
  intros f s stack k le m t next FIN STACK ACTIVE STEP.
  destruct s; simpl in FIN; try discriminate.
  - destruct stack as [|r rest]; [destruct ACTIVE; contradiction |].
    simpl in STEP. inversion STEP; subst; try contradiction;
      try match goal with H : is_call_cont (Kseq _ _) |- _ => contradiction end.
    eexists; eexists; eexists; eexists; repeat split; eauto using fs_pop.
  - inversion STEP; subst;
      try match goal with H : _ = _ \/ _ = _ |- _ => destruct H; discriminate end.
    exists Sskip, stack; eexists; eexists;
      repeat split; eauto using fs_assign.
  - inversion STEP; subst;
      try match goal with H : _ = _ \/ _ = _ |- _ => destruct H; discriminate end.
    exists Sskip, stack; eexists; eexists;
      repeat split; eauto using fs_set.
  - inversion STEP; subst;
      try match goal with H : _ = _ \/ _ = _ |- _ => destruct H; discriminate end.
    exists s1, (s2 :: stack); eexists; eexists;
      repeat split; eauto using fs_seq.
  - inversion STEP; subst;
      try match goal with H : _ = _ \/ _ = _ |- _ => destruct H; discriminate end.
    exists (if b then s1 else s2), stack; eexists; eexists;
      repeat split; eauto using fs_if.
Qed.

Lemma completed_execution le m : resumed_execution Sskip [] le m le m.
Proof. exists le, m; split; constructor. Qed.

Lemma initial_execution s le m le' m' :
  resumed_execution s [] le m le' m' -> exec_stmt fe ge e le m s E0 le' m' Out_normal.
Proof. intros [le1 [m1 [RUN TAIL]]]; inversion TAIL; subst; exact RUN. Qed.
End REGION.

Lemma finite_statement_label_free : forall s,
  finite_statement s = true -> label_free s = true.
Proof.
  induction s; simpl; try discriminate; auto;
    rewrite !andb_true_iff; intros [L R]; split; auto.
Qed.

Print Assumptions fragment_step_from_ambient.
Print Assumptions fragment_step_prepend.
