From Stdlib Require Import List Bool Arith Lia.
From compcert.lib Require Import Maps.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import SilentRegionProtocol ClightGuard ClightFiniteRegion
  ClightRegionProtocol ClightCountedLoop ClightCountedProtocol.
Import ListNotations.
Set Implicit Arguments.

(** Program rewriting keeps symbols and composite layouts. Source-region
    completion can be interpreted in the rewritten global environment. *)
Definition preserving_globals (ge tge : genv) : Prop :=
  genv_cenv tge = genv_cenv ge /\
    forall id, Genv.find_symbol tge id = Genv.find_symbol ge id.

Lemma region_expressions_preserved ge tge : preserving_globals ge tge ->
  forall e le m,
  (forall a v, eval_expr ge e le m a v -> eval_expr tge e le m a v) /\
  (forall a b ofs bf, eval_lvalue ge e le m a b ofs bf ->
    eval_lvalue tge e le m a b ofs bf).
Proof.
  intros [LAYOUT SYMBOLS] e le m; apply eval_expr_lvalue_ind; intros;
    try solve [econstructor; eauto; rewrite LAYOUT; eauto].
  - replace (sizeof ge ty1) with (sizeof tge ty1) by (rewrite LAYOUT; reflexivity).
    constructor.
  - replace (alignof ge ty1) with (alignof tge ty1) by (rewrite LAYOUT; reflexivity).
    constructor.
  - apply eval_Evar_global; auto. rewrite SYMBOLS; auto.
Qed.

(** This class allows loops, but no calls, labels, jumps or return exits. *)
Fixpoint quiet_statement (s : statement) : bool :=
  match s with
  | Sskip | Sassign _ _ | Sset _ _ | Sbreak | Scontinue => true
  | Ssequence l r | Sifthenelse _ l r | Sloop l r => quiet_statement l && quiet_statement r
  | _ => false
  end.

Lemma quiet_execution_preserved fe tfe ge tge : preserving_globals ge tge ->
  forall e le m code trace le' m' outcome,
  exec_stmt fe ge e le m code trace le' m' outcome -> quiet_statement code = true ->
  exec_stmt tfe tge e le m code trace le' m' outcome.
Proof.
  intros GLOBALS e le m code trace le' m' outcome RUN.
  induction RUN; intro QUIET; cbn [quiet_statement] in QUIET; try discriminate;
    try apply andb_true_iff in QUIET as [LEFT RIGHT];
    try solve [econstructor; eauto].
  - eapply exec_Sassign; eauto.
    + eapply (proj2 (region_expressions_preserved GLOBALS e le m)); eauto.
    + eapply (proj1 (region_expressions_preserved GLOBALS e le m)); eauto.
    + destruct GLOBALS as [LAYOUT SYMBOLS]. rewrite LAYOUT; eassumption.
  - econstructor. eapply (proj1 (region_expressions_preserved GLOBALS e le m)); eauto.
  - eapply exec_Sifthenelse; eauto.
    + eapply (proj1 (region_expressions_preserved GLOBALS e le m)); eauto.
    + apply IHRUN. destruct b; assumption.
  - eapply exec_Sloop_loop;
      [apply IHRUN1; exact LEFT | eassumption | apply IHRUN2; exact RIGHT |].
    apply IHRUN3. cbn [quiet_statement]; rewrite LEFT, RIGHT; reflexivity.
Qed.

Definition progress_exit_state (fn : function) (outside : cont) (locals : env)
  (result : temp_env * mem) : state :=
  State fn Sskip outside locals (fst result) (snd result).

(** All source-specific execution information is a language instance.
    A host uses these fields without inspecting its cursor representation. *)
Record region_progress (source : statement) := RegionProgress {
  progress_label_free : label_free source = true;
  progress_protocol : forall temps ge fn outside locals,
    silent_protocol state event (temp_env * mem) (adapter_step temps ge)
      (progress_exit_state fn outside locals);
  progress_entry : forall temps ge fn outside locals,
    protocol_entry (progress_protocol temps ge fn outside locals) (temp_env * mem)
      (fun input => State fn source outside locals (fst input) (snd input))
      (fun input result => exec_stmt (adapter_entry temps) ge locals (fst input) (snd input)
        source E0 (fst result) (snd result) Out_normal);
  progress_initial_active : forall temps ge fn outside locals input,
    cursor_done (progress_protocol temps ge fn outside locals)
      (begin_cursor (progress_entry temps ge fn outside locals) input) = None;
  progress_state_shape : forall temps ge fn outside locals c,
    exists code k le m, cursor_state (progress_protocol temps ge fn outside locals) c =
      State fn code k locals le m;
  progress_execution_preserved : forall temps ge tge,
    preserving_globals ge tge -> forall locals le m le' m',
    exec_stmt (adapter_entry temps) ge locals le m source E0 le' m' Out_normal ->
    exec_stmt (adapter_entry temps) tge locals le m source E0 le' m' Out_normal
}.

Print Assumptions quiet_execution_preserved.

Lemma finite_statement_quiet s : finite_statement s = true -> quiet_statement s = true.
Proof.
  induction s; simpl; try discriminate; auto;
    rewrite !andb_true_iff; intros [L R]; split; auto.
Qed.

Lemma quiet_statement_label_free s : quiet_statement s = true -> label_free s = true.
Proof.
  induction s; simpl; try discriminate; auto;
    rewrite !andb_true_iff; intros [L R]; split; auto.
Qed.

Definition finite_pair_entry source (FIN : finite_statement source = true)
  fe ge fn outside locals :
  protocol_entry (@finite_region_protocol fe ge locals fn outside) (temp_env * mem)
    (fun input => State fn source outside locals (fst input) (snd input))
    (fun input result => exec_stmt fe ge locals (fst input) (snd input)
      source E0 (fst result) (snd result) Out_normal).
Proof.
    refine (@ProtocolEntry state event (temp_env * mem) (step ge (fe ge))
      (progress_exit_state fn outside locals)
      (@finite_region_protocol fe ge locals fn outside)
      (temp_env * mem)
      (fun input => State fn source outside locals (fst input) (snd input))
      (fun input result => exec_stmt fe ge locals (fst input) (snd input)
        source E0 (fst result) (snd result) Out_normal)
      (fun input => @FiniteCursor source [] (fst input) (snd input) FIN (Forall_nil _)) _ _).
  - intro input; reflexivity.
  - intros input result RUN; eapply initial_execution; exact RUN.
Defined.

Definition finite_progress source (FIN : finite_statement source = true)
  (ACTIVE : source <> Sskip) : region_progress source.
Proof.
  refine {| progress_label_free := finite_statement_label_free source FIN;
    progress_protocol := fun temps ge fn outside locals =>
      @finite_region_protocol (adapter_entry temps) ge locals fn outside;
    progress_entry := fun temps ge fn outside locals =>
      @finite_pair_entry source FIN (adapter_entry temps) ge fn outside locals |}.
  - intros temps ge fn outside locals input; cbn [cursor_done finite_region_protocol begin_cursor].
    unfold finite_cursor_done; cbn. destruct source; try reflexivity. contradiction.
  - intros temps ge fn outside locals c; destruct c as [code stack le m CODE STACK].
    exists code, (region_cont stack outside), le, m; reflexivity.
  - intros temps ge tge GLOBALS locals le m le' m' RUN.
    eapply quiet_execution_preserved; [exact GLOBALS | exact RUN |].
    apply finite_statement_quiet; exact FIN.
Defined.

Lemma counted_loop_quiet iterator bound body : memory_body body = true ->
  quiet_statement (counted_loop iterator bound body) = true.
Proof.
  intro BODY. unfold counted_loop, counter_increment; cbn [quiet_statement].
  rewrite (finite_statement_quiet body (memory_body_finite body BODY)); reflexivity.
Qed.

Definition counted_progress iterator bound (DISTINCT : iterator <> bound) body
  (BODY : memory_body body = true) : region_progress (counted_loop iterator bound body).
Proof.
  refine {| progress_label_free := quiet_statement_label_free _
      (counted_loop_quiet iterator bound body BODY);
    progress_protocol := fun temps ge fn outside locals =>
      @counted_region_protocol (adapter_entry temps) ge locals fn outside
        iterator bound DISTINCT body BODY;
    progress_entry := fun temps ge fn outside locals =>
      @counted_region_entry (adapter_entry temps) ge locals fn outside
        iterator bound DISTINCT body BODY |}.
  - intros; reflexivity.
  - intros temps ge fn outside locals c; destruct c; cbn [cursor_state counted_region_protocol
      loop_cursor_state]; repeat eexists; reflexivity.
  - intros temps ge tge GLOBALS locals le m le' m' RUN.
    eapply quiet_execution_preserved; [exact GLOBALS | exact RUN |].
    apply counted_loop_quiet; exact BODY.
Defined.

Print Assumptions finite_progress.
Print Assumptions counted_progress.
