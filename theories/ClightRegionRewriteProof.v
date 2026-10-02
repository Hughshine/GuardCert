From Stdlib Require Import Bool List Arith Lia Wellfounded.
From compcert.lib Require Import Coqlib Maps.
From compcert.common Require Import AST Linking Values Memory Events Globalenvs Smallstep.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightGuard ClightGuardProof ClightFiniteRegion ClightRegionRewrite
  CompCertMemoryEquivalence ClightMemorySteps SilentRegionProtocol ClightRegionProtocol.
Local Open Scope nat_scope.

Section CONTINUATIONS.
Variable select : statement -> option statement.
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
  apply match_statement_cases_ind; intros; simpl; try exact I.
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
  - rewrite (proj1 ClightGuardProof.label_free_find_label s
      (finite_statement_label_free s e) lbl k).
    rewrite (proj1 ClightGuardProof.label_free_find_label ts e0 lbl tk). exact I.
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
Variable select : statement -> option statement.
Hypothesis SELECT_SOUND : forall s ts, select s = Some ts -> region_contract s ts.
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

Inductive aligned_states : state -> state -> Prop :=
| aligned_state : forall f s ts k tk e le m,
    match_statement s ts -> related_cont select k tk ->
    aligned_states (State f s k e le m)
      (State (transform_function select f) ts tk e le m)
| aligned_pending : forall f source target cur stack k tk e le0 m0 le m,
    region_contract source target -> related_cont select k tk ->
    finite_statement cur = true -> Forall (fun s => finite_statement s = true) stack ->
    (cur <> Sskip \/ stack <> nil) ->
    (forall le' m', resumed_execution (adapter_entry temps) tge e cur stack le m le' m' ->
       exec_stmt (adapter_entry temps) tge e le0 m0 source E0 le' m' Out_normal) ->
    aligned_states (State f cur (region_cont stack k) e le m)
      (State (transform_function select f) target tk e le0 m0)
| aligned_callstate : forall fd args k tk m,
    related_cont select k tk ->
    aligned_states (Callstate fd args k m)
      (Callstate (transform_fundef select fd) args tk m)
| aligned_returnstate : forall v k tk m,
    related_cont select k tk ->
    aligned_states (Returnstate v k m) (Returnstate v tk m).

(** The local proof may use an aligned memory as a witness.  The actual
    target memory is related by a language-provided context property. *)
Definition match_states source target :=
  exists aligned, aligned_states source aligned /\ memory_related_states aligned target.

Lemma match_states_exact source target :
  aligned_states source target -> match_states source target.
Proof. intro MATCH; exists target; split; [exact MATCH | apply memory_related_states_refl]. Qed.

Lemma match_states_transport source target final :
  match_states source target -> memory_related_states target final -> match_states source final.
Proof.
  intros [aligned [MATCH FIRST]] SECOND; exists aligned; split; [exact MATCH |].
  eapply memory_related_states_trans; eauto.
Qed.

Lemma eval_expr_preserved : forall e le m a v,
  eval_expr ge e le m a v -> eval_expr tge e le m a v.
Proof. intros; eapply (proj1 (expressions_preserved e le m)); eauto. Qed.

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
Local Hint Constructors match_statement match_cases related_cont aligned_states : core.

Ltac inv_statement :=
  match goal with H : match_statement _ _ |- _ => inversion H; subst; clear H end.
Ltac inv_cont :=
  match goal with H : related_cont _ _ _ |- _ => inversion H; subst; clear H end.
Ltac match_exact := apply match_states_exact; econstructor; eauto.
Ltac finish_step :=
  eexists; split; [apply plus_one; unfold adapter_step; eauto 8 using step | econstructor; eauto].

Lemma fragment_step_preserved : forall e s stack le m s' stack' le' m',
  fragment_step ge e s stack le m s' stack' le' m' ->
  fragment_step tge e s stack le m s' stack' le' m'.
Proof.
  intros e s stack le m s' stack' le' m' STEP; inversion STEP; subst;
    econstructor; eauto.
Qed.

Lemma advance_region : forall f source target cur stack k tk e le0 m0 le m t next,
  region_contract source target -> related_cont select k tk ->
  finite_statement cur = true -> Forall (fun s => finite_statement s = true) stack ->
  (cur <> Sskip \/ stack <> nil) ->
  (forall le' m', resumed_execution (adapter_entry temps) tge e cur stack le m le' m' ->
     exec_stmt (adapter_entry temps) tge e le0 m0 source E0 le' m' Out_normal) ->
  adapter_step temps ge (State f cur (region_cont stack k) e le m) t next ->
  exists next_target,
    (plus (adapter_step temps) tge
       (State (transform_function select f) target tk e le0 m0) t next_target \/
     (star (adapter_step temps) tge
       (State (transform_function select f) target tk e le0 m0) t next_target /\
      state_weight next < state_weight (State f cur (region_cont stack k) e le m))) /\
    match_states next next_target.
Proof.
  intros f source target cur stack k tk e le0 m0 le m t next
    CONTRACT CONT FIN STACK ACTIVE PREFIX STEP.
  pose (P := @finite_region_protocol (adapter_entry temps) ge e f k).
  pose (current := @FiniteCursor cur stack le m FIN STACK).
  assert (NOTDONE : cursor_done P current = None).
  { change (finite_cursor_done current = None).
    destruct cur; try reflexivity. destruct stack; [destruct ACTIVE; contradiction | reflexivity]. }
  destruct (cursor_step_closed P current t next NOTDONE STEP)
    as [following [TRACE [NEXT FS]]].
  pose proof (cursor_step_decreases P current following FS) as DECREASE.
  destruct following as [cur' stack' le' m' FIN' STACK'].
  change (t = E0) in TRACE.
  change (next = State f cur' (region_cont stack' k) e le' m') in NEXT.
  change (fragment_step ge e cur stack le m cur' stack' le' m') in FS.
  change (state_weight (State f cur' (region_cont stack' k) e le' m') <
    state_weight (State f cur (region_cont stack k) e le m)) in DECREASE.
  subst t next.
  apply fragment_step_preserved in FS.
  assert (PREFIX' : forall le2 m2,
    resumed_execution (adapter_entry temps) tge e cur' stack' le' m' le2 m2 ->
    exec_stmt (adapter_entry temps) tge e le0 m0 source E0 le2 m2 Out_normal).
  { intros le2 m2 REST; apply PREFIX.
    eapply fragment_step_prepend; eauto. }
  destruct (Nat.eq_dec (statement_weight cur') 0) as [ZERO | NONZERO].
  - apply statement_weight_zero in ZERO; subst cur'.
    destruct stack' as [|rest stack'].
    + destruct (CONTRACT temps tp e le0 m0 le' m'
        (PREFIX' _ _ (completed_execution _ _ _ _ _))
        (transform_function select f) tk) as [target_memory [RUN EQ]].
      exists (State (transform_function select f) Sskip tk e le' target_memory); split.
      * right; split; [exact RUN | exact DECREASE].
      * exists (State (transform_function select f) Sskip tk e le' m'); split;
          [constructor; auto | constructor; exact EQ].
    + exists (State (transform_function select f) target tk e le0 m0); split.
      * right; split; [apply star_refl | exact DECREASE].
      * apply match_states_exact; eapply aligned_pending; eauto. right; discriminate.
  - exists (State (transform_function select f) target tk e le0 m0); split.
    + right; split; [apply star_refl | exact DECREASE].
    + apply match_states_exact; eapply aligned_pending; eauto. left; intro EQ; subst; contradiction.
Qed.

Lemma aligned_step_simulation : forall s1 t s1',
  adapter_step temps ge s1 t s1' -> forall s2, aligned_states s1 s2 ->
  exists s2',
    (plus (adapter_step temps) tge s2 t s2' \/
     (star (adapter_step temps) tge s2 t s2' /\ state_weight s1' < state_weight s1)) /\
    match_states s1' s2'.
Proof.
  intros s1 t s1' STEP s2 MATCH. inversion MATCH; subst.
  2: { eapply advance_region; eauto. }
  - match goal with MS : match_statement _ _ |- _ => inversion MS; subst; clear MS end.
    all: try match goal with CONTRACT : region_contract _ _ |- _ =>
      eapply advance_region with (stack := nil); simpl; eauto;
      [left; intro EQ; subst; simpl in *; lia | intros; eapply initial_execution; eauto]
    end.
    all: inversion STEP; subst;
      try match goal with H : _ = _ \/ _ = _ |- _ => destruct H; subst end.
    all: try discriminate.
    all: try solve [inv_cont; match goal with H : is_call_cont _ |- _ => contradiction end].
    all: try solve [inv_cont; eexists; split;
      [left; apply plus_one; unfold adapter_step; eauto 8 using step |
       match_exact]].
    all: try solve [eexists; split; [left; apply plus_one; unfold adapter_step;
        eauto 8 using step, related_is_call_cont, related_call_cont |
        apply match_states_exact; econstructor; eauto using related_call_cont]].
    + exists (Callstate (transform_fundef select fd) vargs
        (Kcall id (transform_function select f) e le tk) m); split.
      * left; apply plus_one. eapply step_call; eauto.
        -- eapply Genv.find_funct_transf; eauto using program_matches.
        -- rewrite type_of_fundef_preserved; auto.
      * match_exact.
    + eexists; split.
      * left; apply plus_one. eapply step_ifthenelse; eauto.
      * apply match_states_exact; constructor; auto. destruct b; auto.
    + eexists; split.
      * left; apply plus_one. eapply step_switch; eauto.
      * apply match_states_exact; constructor; auto. apply match_seq_cases, match_select_switch; auto.
    + pose proof (proj1 (find_label_match select) _ _
        (proj1 (transform_statement_matches select SELECT_SOUND) (fn_body f))
        lbl _ _ (related_call_cont select k tk ltac:(assumption))) as LABEL.
      match goal with SOURCE_LABEL : find_label _ _ _ = Some _ |- _ =>
        rewrite SOURCE_LABEL in LABEL end.
      destruct (find_label lbl (transform_statement select (fn_body f))
        (call_cont tk)) as [[ts' tk']|] eqn:TLABEL;
        simpl in LABEL; try contradiction.
      destruct LABEL as [MS MK].
      eexists; split; [left; apply plus_one; eapply step_goto; eauto | match_exact].
  - inversion STEP; subst.
    + exists (State (transform_function select f)
        (fn_body (transform_function select f)) tk e le m1); split.
      * left; apply plus_one. eapply step_internal_function. apply entry_preserved; auto.
      * apply match_states_exact; constructor; auto.
        apply (proj1 (transform_statement_matches select SELECT_SOUND)).
    + eexists; split;
        [left; apply plus_one; eapply step_external_function; eauto | match_exact].
  - inversion STEP; subst; inv_cont.
    eexists; split; [left; apply plus_one; unfold adapter_step; eauto using step |
      match_exact].
Qed.

Lemma step_simulation : forall s1 t s1',
  adapter_step temps ge s1 t s1' -> forall s2, match_states s1 s2 ->
  exists s2',
    (plus (adapter_step temps) tge s2 t s2' \/
     (star (adapter_step temps) tge s2 t s2' /\ state_weight s1' < state_weight s1)) /\
    match_states s1' s2'.
Proof.
  intros s1 t s1' STEP s2 [aligned [MATCH EQ]].
  destruct (aligned_step_simulation _ _ _ STEP _ MATCH) as [next [PATH RESULT]].
  destruct PATH as [PLUS | [STAR DECREASE]].
  - destruct (plus_memory_transport _ _ _ _ _ PLUS _ EQ) as [final [RUN RELATED]].
    exists final; split; [left; exact RUN | eapply match_states_transport; eauto].
  - destruct (star_memory_transport _ _ _ _ _ STAR _ EQ) as [final [RUN RELATED]].
    exists final; split; [right; split; assumption | eapply match_states_transport; eauto].
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
  - apply match_states_exact; constructor; constructor.
Qed.

Theorem transform_program_correct :
  forward_simulation (adapter_semantics temps p) (adapter_semantics temps tp).
Proof.
  eapply forward_simulation_star_wf with
    (order := ltof state state_weight) (match_states := match_states).
  - exact (proj1 (proj2 senv_preserved)).
  - exact initial_states_simulation.
  - intros s ts r [aligned [MATCH EQ]] FINAL; inversion FINAL; subst;
      inversion MATCH; subst; inv_cont; inversion EQ; subst; constructor.
  - apply well_founded_ltof.
  - exact step_simulation.
Qed.
End PRESERVATION.

Corollary transform_program_correct2 : forall select,
  (forall s ts, select s = Some ts -> region_contract s ts) -> forall p,
  forward_simulation (semantics2 p) (semantics2 (transform_program select p)).
Proof. intros; exact (transform_program_correct select H true p). Qed.

Print Assumptions transform_program_correct.
