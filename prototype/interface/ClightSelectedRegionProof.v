(** Occurrence-sensitive instantiation of the existing projected-region
    simulation. The structural, memory and progress invariants follow
    ClightPrivateRegionProof; only the transformed functions and the source
    matching theorem change. The frozen original host is not modified. *)
From Stdlib Require Import Bool List Arith Lia Wellfounded.
From compcert.lib Require Import Coqlib Maps.
From compcert.common Require Import AST Linking Values Memory Events Globalenvs Smallstep.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightGuard ClightGuardProof ClightRegionRewrite
  ClightPrivateRegion ClightRegionProgress CompCertMemoryEquivalence ClightMemorySteps
  SilentRegionProtocol ClightTempFrame ClightTempFootprint ClightTempScope.
From GuardInterface Require Import ClightSelectedRegion.
Import Ctypes PrivateRegion.
Local Open Scope nat_scope.
Module SelectedRegionProof.
Section CONTINUATIONS.
Variable live : list ident.
Variable chosen : list ident.
Variable pool : list (ident * type).
Variable supported : statement -> bool.
Variable select : statement -> option statement.
Inductive related_cont : cont -> cont -> Prop :=
| rc_stop : related_cont Kstop Kstop
| rc_seq : forall s ts k tk,
    match_statement live s ts -> related_cont k tk -> related_cont (Kseq s k) (Kseq ts tk)
| rc_loop1 : forall l r tl tr k tk,
    match_statement live l tl -> match_statement live r tr -> related_cont k tk ->
    related_cont (Kloop1 l r k) (Kloop1 tl tr tk)
| rc_loop2 : forall l r tl tr k tk,
    match_statement live l tl -> match_statement live r tr -> related_cont k tk ->
    related_cont (Kloop2 l r k) (Kloop2 tl tr tk)
| rc_switch : forall k tk, related_cont k tk -> related_cont (Kswitch k) (Kswitch tk)
| rc_call : forall id f e le tle k tk,
    temp_agree live le tle -> related_cont k tk -> related_cont (Kcall id f e le k)
      (Kcall id (selected_transform_function chosen pool supported select f) e tle tk).

Lemma related_call_cont : forall k tk,
  related_cont k tk -> related_cont (call_cont k) (call_cont tk).
Proof. intros k tk H; induction H; simpl; auto; constructor; auto. Qed.

Lemma related_is_call_cont : forall k tk,
  related_cont k tk -> is_call_cont k -> is_call_cont tk.
Proof. intros k tk H; destruct H; simpl; auto. Qed.

Lemma match_seq_cases : forall cases tcases,
  match_cases live cases tcases ->
  match_statement live (seq_of_labeled_statement cases) (seq_of_labeled_statement tcases).
Proof. intros cases tcases H; induction H; simpl; constructor; auto. Qed.

Lemma match_select_default : forall cases tcases,
  match_cases live cases tcases ->
  match_cases live (select_switch_default cases) (select_switch_default tcases).
Proof. intros cases tcases H; induction H; simpl; [constructor|].
  destruct tag; auto; constructor; auto.
Qed.

Lemma match_select_case : forall n cases tcases,
  match_cases live cases tcases ->
  match (select_switch_case n cases), (select_switch_case n tcases) with
  | Some c, Some tc => match_cases live c tc
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros n cases tcases H; induction H; simpl; auto.
  destruct tag; simpl; auto. destruct (zeq z n); auto; constructor; auto.
Qed.

Lemma match_select_switch : forall n cases tcases,
  match_cases live cases tcases ->
  match_cases live (select_switch n cases) (select_switch n tcases).
Proof.
  intros n cases tcases H. pose proof (match_select_case n _ _ H) as HC.
  unfold select_switch.
  destruct (select_switch_case n cases), (select_switch_case n tcases);
    try contradiction; auto. apply match_select_default; auto.
Qed.

Lemma find_label_match :
  (forall s ts, match_statement live s ts -> forall lbl k tk,
    related_cont k tk ->
    match find_label lbl s k, find_label lbl ts tk with
    | Some (s', k'), Some (ts', tk') => match_statement live s' ts' /\ related_cont k' tk'
    | None, None => True
    | _, _ => False
    end) /\
  (forall cases tcases, match_cases live cases tcases -> forall lbl k tk,
    related_cont k tk ->
    match find_label_ls lbl cases k, find_label_ls lbl tcases tk with
    | Some (s', k'), Some (ts', tk') => match_statement live s' ts' /\ related_cont k' tk'
    | None, None => True
    | _, _ => False
    end).
Proof.
  apply (match_statement_cases_ind live); intros; simpl; try exact I.
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
  - match goal with MODEL : region_progress ?s, LABEL : label_free ?ts = true |- _ =>
      rewrite (proj1 ClightGuardProof.label_free_find_label s (progress_label_free MODEL) lbl k);
      rewrite (proj1 ClightGuardProof.label_free_find_label ts LABEL lbl tk); exact I
    end.
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
Variable live : list ident.
Variable chosen : list ident.
Variable pool : list (ident * type).
Variable supported : statement -> bool.
Variable select : statement -> option statement.
Hypothesis SUPPORTED_SOUND : forall s, supported s = true -> exists MODEL : region_progress s, True.
Hypothesis SELECT_SOUND : forall s ts, select s = Some ts -> projected_region_contract live s ts.
Variable temps : bool.
Variable p : Clight.program.
Hypothesis PROGRAM_SCOPE : program_scope live p.
Hypothesis POOL_FRESH : forall id, In id live -> ~ In id (var_names pool).
Let tp := selected_transform_program chosen pool supported select p.
Let ge := globalenv p.
Let tge := globalenv tp.

Lemma program_matches :
  match_program (fun _ fd tfd => tfd = selected_transform_fundef chosen pool supported select fd) eq p tp.
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

Lemma exprlist_globals_preserved : forall e le m al tys vl,
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

Inductive structural_match : statement -> statement -> Prop :=
| sm_skip : structural_match Sskip Sskip
| sm_assign : forall l r, structural_match (Sassign l r) (Sassign l r)
| sm_set : forall id a, structural_match (Sset id a) (Sset id a)
| sm_call : forall id a args, structural_match (Scall id a args) (Scall id a args)
| sm_builtin : forall id ef tys args,
    structural_match (Sbuiltin id ef tys args) (Sbuiltin id ef tys args)
| sm_seq : forall l r tl tr, match_statement live l tl -> match_statement live r tr ->
    structural_match (Ssequence l r) (Ssequence tl tr)
| sm_if : forall a l r tl tr, match_statement live l tl -> match_statement live r tr ->
    structural_match (Sifthenelse a l r) (Sifthenelse a tl tr)
| sm_loop : forall l r tl tr, match_statement live l tl -> match_statement live r tr ->
    structural_match (Sloop l r) (Sloop tl tr)
| sm_break : structural_match Sbreak Sbreak
| sm_continue : structural_match Scontinue Scontinue
| sm_return : forall a, structural_match (Sreturn a) (Sreturn a)
| sm_switch : forall a cases tcases, match_cases live cases tcases ->
    structural_match (Sswitch a cases) (Sswitch a tcases)
| sm_label : forall lbl s ts, match_statement live s ts ->
    structural_match (Slabel lbl s) (Slabel lbl ts)
| sm_goto : forall lbl, structural_match (Sgoto lbl) (Sgoto lbl).

Inductive aligned_states : nat -> state -> state -> Prop :=
| aligned_state : forall f s ts k tk e le tle m,
    temp_agree live le tle ->
    structural_match s ts -> related_cont live chosen pool supported select k tk ->
    aligned_states 0 (State f s k e le m)
      (State (selected_transform_function chosen pool supported select f) ts tk e tle m)
| aligned_pending : forall f source target k tk e le0 tle0 m0 (MODEL : region_progress source)
    (current : cursor (progress_protocol MODEL temps ge f k e)),
    statement_scope live source -> temp_agree live le0 tle0 ->
    projected_region_contract live source target -> related_cont live chosen pool supported select k tk ->
    cursor_done (progress_protocol MODEL temps ge f k e) current = None ->
    (forall result, cursor_completion (progress_protocol MODEL temps ge f k e) current result ->
      exec_stmt (adapter_entry temps) tge e le0 m0 source E0 (fst result) (snd result) Out_normal) ->
    aligned_states (cursor_rank (progress_protocol MODEL temps ge f k e) current)
      (cursor_state (progress_protocol MODEL temps ge f k e) current)
      (State (selected_transform_function chosen pool supported select f) target tk e tle0 m0)
| aligned_callstate : forall fd args k tk m,
    related_cont live chosen pool supported select k tk ->
    aligned_states 0 (Callstate fd args k m)
      (Callstate (selected_transform_fundef chosen pool supported select fd) args tk m)
| aligned_returnstate : forall v k tk m,
    related_cont live chosen pool supported select k tk ->
    aligned_states 0 (Returnstate v k m) (Returnstate v tk m).

Definition match_states index source target :=
  state_scope live source /\
  exists aligned, aligned_states index source aligned /\ memory_related_states aligned target.

Lemma match_states_exact index source target :
  state_scope live source -> aligned_states index source target -> match_states index source target.
Proof. intros SCOPE MATCH; split; [exact SCOPE|]; exists target; split; [exact MATCH | apply memory_related_states_refl]. Qed.

Lemma match_states_transport index source target final :
  match_states index source target -> memory_related_states target final -> match_states index source final.
Proof.
  intros [SCOPE [aligned [MATCH FIRST]]] SECOND; split; [exact SCOPE|]; exists aligned; split; [exact MATCH |].
  eapply memory_related_states_trans; eauto.
Qed.

Local Hint Constructors structural_match : core.

Lemma alignment_of_statement f s ts k tk e le tle m :
  statement_scope live s -> temp_agree live le tle ->
  match_statement live s ts -> related_cont live chosen pool supported select k tk ->
  exists index, aligned_states index (State f s k e le m)
    (State (selected_transform_function chosen pool supported select f) ts tk e tle m).
Proof.
  intros SCOPE AGREE MS CONT; inversion MS; subst;
    try solve [exists 0; apply aligned_state; [exact AGREE|constructor; eauto | exact CONT]].
  pose (P := progress_protocol MODEL temps ge f k e).
  pose (ENTRY := progress_entry MODEL temps ge f k e).
  pose (current := begin_cursor ENTRY (le, m)).
  exists (cursor_rank P current).
  pose proof (begin_state ENTRY (le, m)) as INITIAL.
  change (cursor_state P current = State f s k e le m) in INITIAL.
  rewrite <- INITIAL.
  eapply aligned_pending with (MODEL := MODEL) (current := current); eauto.
  - exact (progress_initial_active MODEL temps ge f k e (le, m)).
  - intros result REST. eapply (@progress_execution_preserved s MODEL temps ge tge).
    + split; [exact comp_env_preserved | exact symbols_preserved].
    + eapply (begin_completion ENTRY) with (input := (le, m)) (result := result); exact REST.
Qed.

Lemma advance_region f source target k tk e le0 tle0 m0 (MODEL : region_progress source)
  (current : cursor (progress_protocol MODEL temps ge f k e)) events next :
  statement_scope live source -> temp_agree live le0 tle0 ->
  projected_region_contract live source target -> related_cont live chosen pool supported select k tk ->
  cursor_done (progress_protocol MODEL temps ge f k e) current = None ->
  (forall result, cursor_completion (progress_protocol MODEL temps ge f k e) current result ->
    exec_stmt (adapter_entry temps) tge e le0 m0 source E0 (fst result) (snd result) Out_normal) ->
  state_scope live next ->
  adapter_step temps (ge) (cursor_state (progress_protocol MODEL temps ge f k e) current) events next ->
  exists index, exists next_target,
    (plus (adapter_step temps) tge
      (State (selected_transform_function chosen pool supported select f) target tk e tle0 m0) events next_target \/
     (star (adapter_step temps) tge
      (State (selected_transform_function chosen pool supported select f) target tk e tle0 m0) events next_target /\
      index < cursor_rank (progress_protocol MODEL temps ge f k e) current)) /\
    match_states index next next_target.
Proof.
  intros SOURCE_SCOPE AGREE CONTRACT CONT ACTIVE PREFIX NEXT_SCOPE STEP.
  pose (P := progress_protocol MODEL temps ge f k e).
  destruct (cursor_step_closed P current events next ACTIVE STEP)
    as [following [TRACE [NEXT MOVE]]]. subst events next.
  pose proof (cursor_step_decreases P current following MOVE) as DECREASE.
  assert (PREFIX' : forall result, cursor_completion P following result ->
    exec_stmt (adapter_entry temps) tge e le0 m0 source E0 (fst result) (snd result) Out_normal).
  { intros result REST; apply PREFIX. eapply cursor_completion_prepend; eauto. }
  destruct (cursor_done P following) as [[le' m']|] eqn:DONE.
  - pose proof (cursor_done_completion P following DONE) as COMPLETE.
    destruct (CONTRACT temps tp e le0 tle0 m0 le' m' SOURCE_SCOPE AGREE (PREFIX' _ COMPLETE)
      (selected_transform_function chosen pool supported select f) tk) as [target_temps [target_memory [RUN [EXIT_AGREE EQ]]]].
    exists 0, (State (selected_transform_function chosen pool supported select f) Sskip tk e target_temps target_memory); split.
    + right; split; [exact RUN | change (0 < cursor_rank P current); lia].
    + rewrite (cursor_done_state P following DONE) in NEXT_SCOPE |- *.
      split; [exact NEXT_SCOPE|].
      exists (State (selected_transform_function chosen pool supported select f) Sskip tk e target_temps m'); split.
      * apply aligned_state; [exact EXIT_AGREE|constructor | exact CONT].
      * constructor; exact EQ.
  - exists (cursor_rank P following),
      (State (selected_transform_function chosen pool supported select f) target tk e tle0 m0); split.
    + right; split; [apply star_refl | exact DECREASE].
    + apply match_states_exact; [exact NEXT_SCOPE|]. eapply aligned_pending; eauto.
Qed.

Lemma eval_expr_preserved : forall e le tle m a v,
  expression_scope live a -> temp_agree live le tle ->
  eval_expr ge e le m a v -> eval_expr tge e tle m a v.
Proof. intros; eapply expression_temp_transport; eauto.
  eapply (proj1 (expressions_preserved e le m)); eauto.
Qed.
Lemma eval_lvalue_preserved : forall e le tle m a b ofs bf,
  expression_scope live a -> temp_agree live le tle ->
  eval_lvalue ge e le m a b ofs bf -> eval_lvalue tge e tle m a b ofs bf.
Proof. intros; eapply lvalue_temp_transport; eauto.
  eapply (proj2 (expressions_preserved e le m)); eauto.
Qed.
Lemma exprlist_preserved : forall e le tle m args tys values,
  expressions_scope live args -> temp_agree live le tle ->
  eval_exprlist ge e le m args tys values -> eval_exprlist tge e tle m args tys values.
Proof. intros; eapply exprlist_temp_transport; eauto using exprlist_globals_preserved. Qed.

Lemma type_of_fundef_preserved : forall fd,
  type_of_fundef (selected_transform_fundef chosen pool supported select fd) = type_of_fundef fd.
Proof. intros []; reflexivity. Qed.

Lemma entry_preserved : forall f args m e le m',
  function_scope live f -> adapter_entry temps ge f args m e le m' ->
  exists tle, adapter_entry temps tge (selected_transform_function chosen pool supported select f) args m e tle m' /\
    temp_agree live le tle.
Proof.
  intros f args m e le m' SCOPE ENTRY; unfold adapter_entry in *;
    destruct temps; inversion ENTRY; subst.
  - destruct (@bind_parameters_temp_agree (fn_params f) args
      (create_undef_temps (fn_temps f)) (create_undef_temps (fn_temps f ++ pool)) le live
      (@temp_agree_undef_append live (fn_temps f) pool POOL_FRESH) H3)
      as [tle [BIND AGREE]].
    exists tle; split; [|exact AGREE].
    econstructor; cbn; eauto using alloc_preserved.
    unfold var_names; rewrite map_app.
    intros id id' PARAM DECL; apply in_app_iff in DECL as [OLD|NEW].
    + eapply H1; eauto.
    + intro SAME; subst id'; eapply POOL_FRESH; [eapply function_scope_params; eauto|exact NEW].
  - exists (create_undef_temps (fn_temps f ++ pool)); split.
    + econstructor; cbn; eauto using alloc_preserved, bind_preserved.
    + apply temp_agree_undef_append; exact POOL_FRESH.
Qed.

Lemma external_preserved : forall ef args m t v m',
  external_call ef ge args m t v m' -> external_call ef tge args m t v m'.
Proof. intros; eapply external_call_symbols_preserved; eauto using senv_preserved. Qed.

Local Hint Resolve eval_expr_preserved eval_lvalue_preserved exprlist_preserved
  external_preserved match_seq_cases match_select_switch
  related_call_cont related_is_call_cont temp_agree_set_both temp_agree_opttemp
  scope_append_left scope_append_right scope_cons_tail scope_cons_head : core.
Local Hint Constructors match_statement match_cases related_cont structural_match : core.
Local Hint Unfold expression_scope expressions_scope : core.

Ltac inv_cont :=
  match goal with H : related_cont _ _ _ _ _ _ _ |- _ => inversion H; subst; clear H end.
Ltac match_exact NEXT_SCOPE :=
  first [
    match goal with
    | |- exists index, match_states index (State ?f ?s ?k ?e ?le ?m)
        (State ?tf ?ts ?tk ?te ?tle ?tm) =>
      let MS := fresh "MS" in assert (MS : match_statement live s ts) by eauto;
      let CT := fresh "CT" in assert (CT : related_cont live chosen pool supported select k tk) by eauto;
      let SC := fresh "SC" in assert (SC : statement_scope live s)
        by (change (function_scope live f /\ statement_scope live s /\ continuation_scope live k) in NEXT_SCOPE; tauto);
      let EQ := fresh "EQ" in assert (EQ : temp_agree live le tle) by eauto;
      let index := fresh "next_index" in let AL := fresh "AL" in
      destruct (alignment_of_statement f s ts k tk e le tle m SC EQ MS CT) as [index AL];
      exists index; apply match_states_exact; [exact NEXT_SCOPE|exact AL]
    end
  | exists 0; apply match_states_exact; [exact NEXT_SCOPE|constructor; eauto] ].

Lemma structural_step_simulation f s ts k tk e le tle m events next :
  state_scope live (State f s k e le m) -> temp_agree live le tle ->
  adapter_step temps ge (State f s k e le m) events next ->
  structural_match s ts -> related_cont live chosen pool supported select k tk ->
  exists next_target,
    plus (adapter_step temps) tge
      (State (selected_transform_function chosen pool supported select f) ts tk e tle m) events next_target /\
    exists index, match_states index next next_target.
Proof.
  intros SCOPE AGREE STEP MS CONT.
  pose proof (step_preserves_temp_scope PROGRAM_SCOPE SCOPE STEP) as NEXT_SCOPE.
  destruct SCOPE as [FUNCTION_SCOPE [CODE CONT_SCOPE]].
  inversion MS; subst.
    all: inversion STEP; subst;
      try match goal with H : _ = _ \/ _ = _ |- _ => destruct H; subst end.
    all: unfold statement_scope in CODE; cbn [statement_temps optional_expression_temps] in CODE.
    all: try discriminate.
    all: try solve [inv_cont; match goal with H : is_call_cont _ |- _ => contradiction end].
    all: try solve [inv_cont; eexists; split;
      [apply plus_one; unfold adapter_step; eauto 8 using step |
       match_exact NEXT_SCOPE]].
    all: try solve [eexists; split; [apply plus_one; unfold adapter_step;
        eauto 8 using step, related_is_call_cont, related_call_cont |
        match_exact NEXT_SCOPE]].
    + exists (Callstate (selected_transform_fundef chosen pool supported select fd) vargs
        (Kcall id (selected_transform_function chosen pool supported select f) e tle tk) m); split.
      * apply plus_one. eapply step_call; eauto.
        -- eapply Genv.find_funct_transf; eauto using program_matches.
        -- rewrite type_of_fundef_preserved; auto.
      * match_exact NEXT_SCOPE.
    + eexists; split.
      * apply plus_one. eapply step_ifthenelse; eauto.
      * destruct b; match_exact NEXT_SCOPE.
    + pose proof (proj1 (find_label_match live chosen pool supported select) _ _
        (proj1 (@selected_transform_matches live chosen supported select SUPPORTED_SOUND SELECT_SOUND) (fn_body f))
        lbl _ _ (related_call_cont live chosen pool supported select k tk ltac:(assumption))) as LABEL.
      match goal with SOURCE_LABEL : find_label _ _ _ = Some _ |- _ =>
        rewrite SOURCE_LABEL in LABEL end.
      destruct (find_label lbl (selected_transform_statement chosen supported select false (fn_body f))
        (call_cont tk)) as [[ts' tk']|] eqn:TLABEL;
        simpl in LABEL; try contradiction.
      destruct LABEL as [LABEL_MS MK].
      eexists; split; [apply plus_one; eapply step_goto; eauto | match_exact NEXT_SCOPE].
Qed.

Lemma aligned_step_simulation : forall source events next,
  state_scope live source -> adapter_step temps ge source events next -> forall index target,
  aligned_states index source target -> exists next_index, exists next_target,
    (plus (adapter_step temps) tge target events next_target \/
     (star (adapter_step temps) tge target events next_target /\ next_index < index)) /\
    match_states next_index next next_target.
Proof.
  intros source events next SCOPE STEP index target MATCH.
  pose proof (step_preserves_temp_scope PROGRAM_SCOPE SCOPE STEP) as NEXT_SCOPE.
  inversion MATCH; subst.
  - destruct (structural_step_simulation f s ts k tk e le tle m events next SCOPE H STEP H0 H1)
      as [next_target [PATH [next_index NEXT]]].
    exists next_index, next_target; split; [left; exact PATH | exact NEXT].
  - eapply advance_region; eauto.
  - inversion STEP; subst.
    + cbn [state_scope fundef_scope fundef_temps] in SCOPE.
      destruct SCOPE as [FUNCTION_SCOPE CONT_SCOPE].
      assert (BODY_MS : match_statement live (fn_body f)
        (fn_body (selected_transform_function chosen pool supported select f)))
        by (apply (proj1 (@selected_transform_matches live chosen supported select SUPPORTED_SOUND SELECT_SOUND))).
      match goal with ENTRY : adapter_entry temps ge f args m e le m1 |- _ =>
        destruct (entry_preserved f args m e le m1 FUNCTION_SCOPE ENTRY) as [tle [TARGET_ENTRY AGREE]]
      end.
      destruct (alignment_of_statement f (fn_body f)
        (fn_body (selected_transform_function chosen pool supported select f)) k tk e le tle m1
        (function_scope_body FUNCTION_SCOPE) AGREE BODY_MS H)
        as [next_index NEXT].
      exists next_index, (State (selected_transform_function chosen pool supported select f)
        (fn_body (selected_transform_function chosen pool supported select f)) tk e tle m1); split.
      * left; apply plus_one. eapply step_internal_function; exact TARGET_ENTRY.
      * apply match_states_exact; [exact NEXT_SCOPE|exact NEXT].
    + exists 0; eexists; split.
      * left; apply plus_one. eapply step_external_function; eauto.
      * apply match_states_exact; [exact NEXT_SCOPE|constructor; auto].
  - inversion STEP; subst; inv_cont. exists 0; eexists; split.
    + left; apply plus_one; unfold adapter_step; eauto using step.
    + apply match_states_exact; [exact NEXT_SCOPE|].
      apply aligned_state; eauto; constructor.
Qed.

Lemma step_simulation : forall source events next,
  adapter_step temps ge source events next -> forall index target,
  match_states index source target -> exists next_index, exists next_target,
    (plus (adapter_step temps) tge target events next_target \/
     (star (adapter_step temps) tge target events next_target /\ next_index < index)) /\
    match_states next_index next next_target.
Proof.
  intros source events next STEP index target [SCOPE [aligned [MATCH EQ]]].
  destruct (aligned_step_simulation _ _ _ SCOPE STEP _ _ MATCH)
    as [next_index [following [PATH RESULT]]].
  destruct PATH as [PLUS | [STAR DECREASE]].
  - destruct (plus_memory_transport _ _ _ _ _ PLUS _ EQ) as [final [RUN RELATED]].
    exists next_index, final; split; [left; exact RUN | eapply match_states_transport; eauto].
  - destruct (star_memory_transport _ _ _ _ _ STAR _ EQ) as [final [RUN RELATED]].
    exists next_index, final; split; [right; split; assumption | eapply match_states_transport; eauto].
Qed.

Lemma initial_states_simulation : forall source,
  initial_state p source -> exists index, exists target,
    initial_state tp target /\ match_states index source target.
Proof.
  intros source INIT; inversion INIT; subst.
  exists 0, (Callstate (selected_transform_fundef chosen pool supported select f) nil Kstop m0); split.
  - eapply initial_state_intro with (b := b).
    + exact (Genv.init_mem_transf program_matches H).
    + change (Genv.find_symbol tge (prog_main p) = Some b).
      rewrite symbols_preserved; exact H0.
    + eapply Genv.find_funct_ptr_transf; [exact program_matches | exact H1].
    + rewrite type_of_fundef_preserved; auto.
  - apply match_states_exact.
    + cbn; split; [eapply function_scope_ptr_lookup; eauto|exact I].
    + constructor; constructor.
Qed.

Lemma final_states_simulation : forall index source target result,
  match_states index source target -> final_state source result -> final_state target result.
Proof.
  intros index source target result [SCOPE [aligned [MATCH EQ]]] FINAL; inversion FINAL; subst.
  inversion MATCH; subst.
  - match goal with MODEL : region_progress ?s,
      current : cursor (progress_protocol MODEL temps ge ?f ?k ?e) |- _ =>
      destruct (@progress_state_shape s MODEL temps ge f k e current)
        as [code [stack [le [inside_memory SHAPE]]]];
      match goal with
      | BAD : cursor_state _ current = _ |- _ => rewrite SHAPE in BAD; discriminate
      | BAD : _ = cursor_state _ current |- _ => rewrite SHAPE in BAD; discriminate
      end
    end.
  - inv_cont; inversion EQ; subst; constructor.
Qed.

Theorem transform_program_correct :
  forward_simulation (adapter_semantics temps p) (adapter_semantics temps tp).
Proof.
  refine (@Forward_simulation (adapter_semantics temps p) (adapter_semantics temps tp)
    nat lt match_states _). constructor.
  - apply lt_wf.
  - exact initial_states_simulation.
  - exact final_states_simulation.
  - exact step_simulation.
  - exact (proj1 (proj2 senv_preserved)).
Qed.

End PRESERVATION.
Corollary transform_program_correct2 : forall live chosen pool supported select,
  (forall s, supported s = true -> exists MODEL : region_progress s, True) ->
  (forall s ts, select s = Some ts -> projected_region_contract live s ts) -> forall p,
  program_scope live p -> (forall id, In id live -> ~ In id (var_names pool)) ->
  forward_simulation (Clight.semantics2 p)
    (Clight.semantics2 (selected_transform_program chosen pool supported select p)).
Proof. intros; exact (@transform_program_correct live chosen pool supported select H H0 true p H1 H2). Qed.
End SelectedRegionProof.
Print Assumptions SelectedRegionProof.transform_program_correct.
Print Assumptions SelectedRegionProof.transform_program_correct2.
