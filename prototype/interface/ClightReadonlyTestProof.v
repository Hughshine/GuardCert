From Stdlib Require Import Bool List.
From compcert.lib Require Import Coqlib Maps.
From compcert.common Require Import AST Linking Values Memory Events Globalenvs Smallstep.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightGuard ClightCondition ClightTreeRewrite.
From GuardInterface Require Import ClightReadonlyTestSyntax.

Section CONTINUATIONS.
Variable select : expr -> option (decision_tree * expr).
Inductive related_cont : cont -> cont -> Prop :=
| rc_stop : related_cont Kstop Kstop
| rc_seq : forall s ts k tk,
    match_statement s ts -> related_cont k tk -> related_cont (Kseq s k) (Kseq ts tk)
| rc_loop1 : forall l r tl tr k tk,
    match_statement l tl -> match_statement r tr -> related_cont k tk ->
    related_cont (Kloop1 l r k) (Kloop1 tl tr tk)
| rc_loop2 : forall l r tl tr k tk,
    match_statement l tl -> match_statement r tr -> related_cont k tk ->
    related_cont (Kloop2 l r k) (Kloop2 tl tr tk)
| rc_switch : forall k tk, related_cont k tk -> related_cont (Kswitch k) (Kswitch tk)
| rc_call : forall id f e le k tk,
    related_cont k tk -> related_cont (Kcall id f e le k)
      (Kcall id (transform_function select f) e le tk).

Lemma related_call_cont : forall k tk,
  related_cont k tk -> related_cont (call_cont k) (call_cont tk).
Proof. intros k tk H; induction H; simpl; auto; constructor; auto. Qed.

Lemma related_is_call_cont : forall k tk,
  related_cont k tk -> is_call_cont k -> is_call_cont tk.
Proof. intros k tk H; destruct H; simpl; auto. Qed.

Lemma match_seq_cases : forall cases tcases,
  match_cases cases tcases ->
  match_statement (seq_of_labeled_statement cases) (seq_of_labeled_statement tcases).
Proof. intros cases tcases H; induction H; simpl; constructor; auto. Qed.

Lemma match_select_default : forall cases tcases,
  match_cases cases tcases ->
  match_cases (select_switch_default cases) (select_switch_default tcases).
Proof. intros cases tcases H; induction H; simpl; [constructor|].
  destruct tag; auto; constructor; auto.
Qed.

Lemma match_select_case : forall n cases tcases,
  match_cases cases tcases ->
  match (select_switch_case n cases), (select_switch_case n tcases) with
  | Some c, Some tc => match_cases c tc
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros n cases tcases H; induction H; simpl; auto.
  destruct tag; simpl; auto. destruct (zeq z n); auto; constructor; auto.
Qed.

Lemma match_select_switch : forall n cases tcases,
  match_cases cases tcases ->
  match_cases (select_switch n cases) (select_switch n tcases).
Proof.
  intros n cases tcases H. pose proof (match_select_case n _ _ H) as HC.
  unfold select_switch.
  destruct (select_switch_case n cases), (select_switch_case n tcases);
    try contradiction; auto. apply match_select_default; auto.
Qed.

Lemma tree_find_label : forall t lbl yes no k,
  find_label lbl yes k = None -> find_label lbl no k = None ->
  find_label lbl (tree_statement t yes no) k = None.
Proof.
  induction t; intros lbl yes no k Y N; simpl.
  - destruct accept; assumption.
  - rewrite IHt1 by assumption. apply IHt2; assumption.
Qed.

Lemma find_label_match :
  (forall s ts, match_statement s ts -> forall lbl k tk,
    related_cont k tk ->
    match find_label lbl s k, find_label lbl ts tk with
    | Some (s', k'), Some (ts', tk') => match_statement s' ts' /\ related_cont k' tk'
    | None, None => True
    | _, _ => False
    end) /\
  (forall cases tcases, match_cases cases tcases -> forall lbl k tk,
    related_cont k tk ->
    match find_label_ls lbl cases k, find_label_ls lbl tcases tk with
    | Some (s', k'), Some (ts', tk') => match_statement s' ts' /\ related_cont k' tk'
    | None, None => True
    | _, _ => False
    end).
Proof.
  apply match_statement_cases_ind; intros; simpl; try exact I;
    try (rewrite tree_find_label; [exact I | reflexivity | reflexivity]).
  - specialize (H lbl (Kseq r k) (Kseq tr tk) (rc_seq _ _ _ _ m0 H1)).
    destruct (find_label lbl l (Kseq r k)) as [[s' k']|],
      (find_label lbl tl (Kseq tr tk)) as [[ts' tk']|]; try contradiction; auto.
    apply H0; auto.
  - specialize (H lbl k tk H1).
    destruct (find_label lbl l k) as [[s' k']|],
      (find_label lbl tl tk) as [[ts' tk']|]; try contradiction; auto.
    apply H0; auto.
  - specialize (H lbl (Kloop1 l r k) (Kloop1 tl tr tk)
      (rc_loop1 _ _ _ _ _ _ m m0 H1)).
    destruct (find_label lbl l (Kloop1 l r k)) as [[s' k']|],
      (find_label lbl tl (Kloop1 tl tr tk)) as [[ts' tk']|];
      try contradiction; auto.
    apply H0. constructor; auto.
  - apply H. constructor; auto.
  - destruct (ident_eq lbl0 lbl); auto. apply H; auto.
  - specialize (H lbl (Kseq (seq_of_labeled_statement rest) k)
      (Kseq (seq_of_labeled_statement trest) tk)
      (rc_seq _ _ _ _ (match_seq_cases _ _ m0) H1)).
    destruct (find_label lbl s (Kseq (seq_of_labeled_statement rest) k)) as [[s' k']|],
      (find_label lbl ts (Kseq (seq_of_labeled_statement trest) tk)) as [[ts' tk']|];
      try contradiction; auto.
    apply H0; auto.
Qed.
End CONTINUATIONS.

Section PRESERVATION.
Variable select : expr -> option (decision_tree * expr).
Hypothesis SELECT_SOUND : forall a g c, select a = Some (g, c) -> expression_contract a g c.
Variable temps : bool.
Variable p : program.
Let tp := transform_program select p.
Let ge := globalenv p.
Let tge := globalenv tp.

Lemma program_matches :
  match_program (fun _ fd tfd => tfd = transform_fundef select fd) eq p tp.
Proof. apply match_transform_program. Qed.

Lemma comp_env_preserved : genv_cenv tge = genv_cenv ge.
Proof. reflexivity. Qed.

Lemma symbols_preserved : forall id, Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof. exact (Genv.find_symbol_transf program_matches). Qed.

Lemma senv_preserved : Senv.equiv ge tge.
Proof. exact (Genv.senv_transf program_matches). Qed.

Lemma expressions_preserved :
  forall e le m,
  (forall a v, eval_expr ge e le m a v -> eval_expr tge e le m a v) /\
  (forall a b ofs bf, eval_lvalue ge e le m a b ofs bf ->
    eval_lvalue tge e le m a b ofs bf).
Proof.
  intros e le m; apply eval_expr_lvalue_ind; intros;
    try solve [econstructor; eauto].
  - change (sizeof ge ty1) with (sizeof tge ty1). constructor.
  - change (alignof ge ty1) with (alignof tge ty1). constructor.
  - apply eval_Evar_global; auto. rewrite symbols_preserved; auto.
Qed.

Lemma exprlist_preserved : forall e le m al tys vl,
  eval_exprlist ge e le m al tys vl -> eval_exprlist tge e le m al tys vl.
Proof.
  intros e le m al tys vl H; induction H; econstructor; eauto.
  eapply (proj1 (expressions_preserved e le m)); eauto.
Qed.

Lemma alloc_preserved : forall e m vars e' m',
  alloc_variables ge e m vars e' m' -> alloc_variables tge e m vars e' m'.
Proof.
  intros e m vars e' m' H; induction H; econstructor; eauto.
Qed.

Lemma bind_preserved : forall e m params args m',
  bind_parameters ge e m params args m' -> bind_parameters tge e m params args m'.
Proof.
  intros e m params args m' H; induction H; econstructor; eauto.
Qed.

Inductive match_states : state -> state -> Prop :=
| match_state : forall f s ts k tk e le m,
    match_statement s ts -> related_cont select k tk ->
    match_states (State f s k e le m)
      (State (transform_function select f) ts tk e le m)
| match_callstate : forall fd args k tk m,
    related_cont select k tk ->
    match_states (Callstate fd args k m)
      (Callstate (transform_fundef select fd) args tk m)
| match_returnstate : forall v k tk m,
    related_cont select k tk ->
    match_states (Returnstate v k m) (Returnstate v tk m).

Lemma eval_expr_preserved : forall e le m a v,
  eval_expr ge e le m a v -> eval_expr tge e le m a v.
Proof. intros; eapply (proj1 (expressions_preserved e le m)); eauto. Qed.

Lemma decision_preserved : forall e le m t b,
  decision_run (Entry ge e le m) t b -> decision_run (Entry tge e le m) t b.
Proof.
  intros e le m t b RUN; induction RUN.
  - constructor.
  - destruct H as [v [EV BOOL]]. econstructor; eauto.
    exists v; split; auto. apply eval_expr_preserved; exact EV.
Qed.

Lemma eval_lvalue_preserved : forall e le m a b ofs bf,
  eval_lvalue ge e le m a b ofs bf -> eval_lvalue tge e le m a b ofs bf.
Proof. intros; eapply (proj2 (expressions_preserved e le m)); eauto. Qed.

Lemma type_of_fundef_preserved : forall fd,
  type_of_fundef (transform_fundef select fd) = type_of_fundef fd.
Proof. intros []; reflexivity. Qed.

Lemma entry_preserved : forall f args m e le m',
  adapter_entry temps ge f args m e le m' ->
  adapter_entry temps tge (transform_function select f) args m e le m'.
Proof.
  intros f args m e le m' H; unfold adapter_entry in *;
    destruct temps; inversion H; subst;
    econstructor; simpl; eauto using alloc_preserved, bind_preserved.
Qed.

Lemma external_preserved : forall ef args m t v m',
  external_call ef ge args m t v m' -> external_call ef tge args m t v m'.
Proof. intros; eapply external_call_symbols_preserved; eauto using senv_preserved. Qed.

Local Hint Resolve eval_expr_preserved eval_lvalue_preserved exprlist_preserved
  entry_preserved external_preserved : core.
Local Hint Constructors match_statement match_cases related_cont match_states : core.

Ltac inv_statement :=
  match goal with H : match_statement _ _ |- _ => inversion H; subst; clear H end.
Ltac inv_cont :=
  match goal with H : related_cont _ _ _ |- _ => inversion H; subst; clear H end.
Ltac finish_step :=
  eexists; split; [apply plus_one; unfold adapter_step; eauto 8 using step | econstructor; eauto].

Lemma step_simulation : forall s1 t s1',
  adapter_step temps ge s1 t s1' -> forall s2, match_states s1 s2 ->
  exists s2', plus (adapter_step temps) tge s2 t s2' /\ match_states s1' s2'.
Proof.
  intros s1 t s1' STEP s2 MATCH.
  inversion STEP; subst; inversion MATCH; subst.
  - inv_statement.
    + finish_step.
    + match goal with HC : expression_contract _ _ _ |- _ =>
        destruct HC as [TYPE CONTRACT] end.
      destruct (CONTRACT ge e le m v2 H0) as [bg [TREE ACCEPT]].
      apply decision_preserved in TREE.
      destruct bg; eexists; split.
      * eapply plus_right.
        -- eapply decision_dispatch; exact TREE.
        -- eapply step_assign; eauto. rewrite TYPE; eauto.
        -- reflexivity.
      * constructor; auto.
      * eapply plus_right.
        -- eapply decision_dispatch; exact TREE.
        -- eapply step_assign; eauto.
        -- reflexivity.
      * constructor; auto.
  - inv_statement.
    + finish_step.
    + match goal with HC : expression_contract _ _ _ |- _ =>
        destruct HC as [TYPE CONTRACT] end.
      destruct (CONTRACT ge e le m v H) as [bg [TREE ACCEPT]].
      apply decision_preserved in TREE.
      destruct bg; eexists; split.
      * eapply plus_right.
        -- eapply decision_dispatch; exact TREE.
        -- eapply step_set; eauto.
        -- reflexivity.
      * constructor; auto.
      * eapply plus_right.
        -- eapply decision_dispatch; exact TREE.
        -- eapply step_set; eauto.
        -- reflexivity.
      * constructor; auto.
  - inv_statement.
    exists (Callstate (transform_fundef select fd) vargs
      (Kcall optid (transform_function select f) e le tk) m); split.
    + apply plus_one. eapply step_call; eauto.
      * eapply Genv.find_funct_transf; eauto using program_matches.
      * rewrite type_of_fundef_preserved; auto.
    + constructor; auto.
  - inv_statement; finish_step.
  - inv_statement; finish_step.
  - inv_statement; inv_cont; finish_step.
  - inv_statement; inv_cont; finish_step.
  - inv_statement; inv_cont; finish_step.
  - inv_statement.
    + eexists; split; [apply plus_one; eapply step_ifthenelse; eauto|].
      constructor; auto. destruct b; auto.
    + match goal with HC : expression_contract _ _ _ |- _ => destruct HC as [TYPE CONTRACT] end.
      match goal with EVAL : eval_expr ge e le m _ ?value |- _ =>
        destruct (CONTRACT ge e le m value EVAL) as [bg [TREE ACCEPT]] end.
      apply decision_preserved in TREE.
      destruct bg; eexists; split.
      * eapply plus_right.
        -- eapply decision_dispatch; exact TREE.
        -- eapply step_ifthenelse with (b := b); eauto. rewrite TYPE; eauto.
        -- reflexivity.
      * constructor; auto; destruct b; constructor.
      * eapply plus_right.
        -- eapply decision_dispatch; exact TREE.
        -- eapply step_ifthenelse with (b := b); eauto.
        -- reflexivity.
      * constructor; auto; destruct b; constructor.
  - inv_statement; finish_step.
  - destruct H as [H|H]; subst x; inv_statement; inv_cont; finish_step.
  - inv_statement; inv_cont; finish_step.
  - inv_statement; inv_cont; finish_step.
  - inv_statement; inv_cont; finish_step.
  - inv_statement; eexists; split.
    + apply plus_one. eapply step_return_0; eauto.
    + constructor. apply related_call_cont; auto.
  - inv_statement.
    + eexists; split.
      * apply plus_one. eapply step_return_1; eauto.
      * constructor. apply related_call_cont; auto.
    + match goal with HC : expression_contract _ _ _ |- _ =>
        destruct HC as [TYPE CONTRACT] end.
      destruct (CONTRACT ge e le m v H) as [bg [TREE ACCEPT]].
      apply decision_preserved in TREE.
      destruct bg; eexists; split.
      * eapply plus_right.
        -- eapply decision_dispatch; exact TREE.
        -- eapply step_return_1; eauto. rewrite TYPE; eauto.
        -- reflexivity.
      * constructor. apply related_call_cont; auto.
      * eapply plus_right.
        -- eapply decision_dispatch; exact TREE.
        -- eapply step_return_1; eauto.
        -- reflexivity.
      * constructor. apply related_call_cont; auto.
  - inv_statement; eexists; split.
    + apply plus_one. eapply step_skip_call; eauto.
      eapply related_is_call_cont; eauto.
    + constructor; auto.
  - inv_statement; eexists; split.
    + apply plus_one. eapply step_switch; eauto.
    + constructor; auto. apply match_seq_cases. apply match_select_switch; auto.
  - destruct H as [H|H]; subst x; inv_statement; inv_cont; finish_step.
  - inv_statement; inv_cont; finish_step.
  - inv_statement; finish_step.
  - inv_statement.
    pose proof (proj1 (find_label_match select) _ _
      (proj1 (transform_statement_matches select SELECT_SOUND) (fn_body f))
      lbl _ _ (related_call_cont select k tk ltac:(assumption))) as LABEL.
    rewrite H in LABEL.
    destruct (find_label lbl (transform_statement select (fn_body f))
      (call_cont tk)) as [[ts' tk']|] eqn:TLABEL;
      simpl in LABEL; try contradiction.
    destruct LABEL as [MS MK].
    eexists; split; [apply plus_one; eapply step_goto; eauto|constructor; auto].
  - exists (State (transform_function select f)
      (fn_body (transform_function select f)) tk e le m1); split.
    + apply plus_one. eapply step_internal_function. apply entry_preserved; auto.
    + constructor; auto. apply (proj1 (transform_statement_matches select SELECT_SOUND)).
  - eexists; split; [apply plus_one; eapply step_external_function; eauto|constructor; auto].
  - inv_cont; finish_step.
Qed.

Lemma initial_states_simulation : forall s,
  initial_state p s -> exists ts, initial_state tp ts /\ match_states s ts.
Proof.
  intros s INIT; inversion INIT; subst.
  exists (Callstate (transform_fundef select f) nil Kstop m0); split.
  - eapply initial_state_intro with (b := b).
    + exact (Genv.init_mem_transf program_matches H).
    + change (Genv.find_symbol tge (prog_main p) = Some b).
      rewrite symbols_preserved; exact H0.
    + eapply (Genv.find_funct_ptr_transf program_matches); exact H1.
    + rewrite type_of_fundef_preserved; auto.
  - constructor; constructor.
Qed.

Theorem transform_program_correct :
  forward_simulation (adapter_semantics temps p) (adapter_semantics temps tp).
Proof.
  eapply forward_simulation_plus with (match_states := match_states).
  - exact (proj1 (proj2 senv_preserved)).
  - exact initial_states_simulation.
  - intros s ts r MATCH FINAL; inversion FINAL; subst;
      inversion MATCH; subst; inv_cont; constructor.
  - exact step_simulation.
Qed.

End PRESERVATION.

Corollary transform_program_correct1 : forall select,
  (forall a g c, select a = Some (g, c) -> expression_contract a g c) -> forall p,
  forward_simulation (semantics1 p) (semantics1 (transform_program select p)).
Proof. intros; exact (transform_program_correct select H false p). Qed.

Corollary transform_program_correct2 : forall select,
  (forall a g c, select a = Some (g, c) -> expression_contract a g c) -> forall p,
  forward_simulation (semantics2 p) (semantics2 (transform_program select p)).
Proof. intros; exact (transform_program_correct select H true p). Qed.

Print Assumptions transform_program_correct.

Print Assumptions step_simulation.
Print Assumptions transform_program_correct2.
