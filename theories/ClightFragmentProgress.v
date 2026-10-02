From Stdlib Require Import List Bool Arith Lia.
From compcert.lib Require Import Coqlib Maps.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import SilentRegionProtocol ClightGuard ClightFiniteRegion
  ClightRegionProtocol ClightRegionProgress.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope nat_scope.

Definition preserves_temporaries (protected : list ident) (before after : temp_env) : Prop :=
  forall id, In id protected -> after ! id = before ! id.

(** A nullable fragment can serve as a loop body or sequence component. The
    bound concerns its own steps, independently of the enclosing continuation.
    All active steps preserve the declared temporary frame. *)
Record framed_progress (source : statement) (protected : list ident) := FramedProgress {
  framed_quiet : quiet_statement source = true;
  framed_protocol : forall temps ge fn outside locals,
    silent_protocol state event (temp_env * mem) (adapter_step temps ge)
      (progress_exit_state fn outside locals);
  framed_entry : forall temps ge fn outside locals,
    protocol_entry (framed_protocol temps ge fn outside locals) (temp_env * mem)
      (fun input => State fn source outside locals (fst input) (snd input))
      (fun input result => exec_stmt (adapter_entry temps) ge locals (fst input) (snd input)
        source E0 (fst result) (snd result) Out_normal);
  framed_view : forall temps ge fn outside locals,
    cursor (framed_protocol temps ge fn outside locals) -> temp_env * mem;
  framed_shape : forall temps ge fn outside locals c,
    exists code k, cursor_state (framed_protocol temps ge fn outside locals) c =
      State fn code k locals (fst (framed_view temps ge fn outside locals c))
        (snd (framed_view temps ge fn outside locals c));
  framed_begin_view : forall temps ge fn outside locals input,
    framed_view temps ge fn outside locals
      (begin_cursor (framed_entry temps ge fn outside locals) input) = input;
  framed_bound : nat;
  framed_begin_bound : forall temps ge fn outside locals input,
    cursor_rank (framed_protocol temps ge fn outside locals)
      (begin_cursor (framed_entry temps ge fn outside locals) input) <= framed_bound;
  framed_done_rank : forall temps ge fn outside locals c result,
    cursor_done (framed_protocol temps ge fn outside locals) c = Some result ->
    cursor_rank (framed_protocol temps ge fn outside locals) c = 0;
  framed_step_frame : forall temps ge fn outside locals c next,
    cursor_step (framed_protocol temps ge fn outside locals) c next ->
    preserves_temporaries protected (fst (framed_view temps ge fn outside locals c))
      (fst (framed_view temps ge fn outside locals next))
}.

Lemma framed_done_view source protected (F : framed_progress source protected)
  temps ge fn outside locals c result :
  cursor_done (framed_protocol F temps ge fn outside locals) c = Some result ->
  framed_view F temps ge fn outside locals c = result.
Proof.
  intro DONE; destruct (framed_shape F temps ge fn outside locals c) as [code [k SHAPE]].
  pose proof (cursor_done_state (framed_protocol F temps ge fn outside locals) c DONE) as STATE.
  rewrite SHAPE in STATE; destruct (framed_view F temps ge fn outside locals c), result;
    inversion STATE; reflexivity.
Qed.

Fixpoint frame_statement (protected : list ident) (code : statement) : bool :=
  match code with
  | Sskip | Sassign _ _ => true
  | Sset id _ => if in_dec peq id protected then false else true
  | Ssequence l r | Sifthenelse _ l r => frame_statement protected l && frame_statement protected r
  | _ => false
  end.

Lemma frame_statement_finite protected code : frame_statement protected code = true ->
  finite_statement code = true.
Proof.
  induction code; simpl; try discriminate; auto.
  all: rewrite !andb_true_iff; intros [L R]; split; auto.
Qed.

Lemma frame_statement_step protected ge locals code stack le m code' stack' le' m' :
  fragment_step ge locals code stack le m code' stack' le' m' ->
  frame_statement protected code = true ->
  Forall (fun s => frame_statement protected s = true) stack ->
  preserves_temporaries protected le le' /\ frame_statement protected code' = true /\
    Forall (fun s => frame_statement protected s = true) stack'.
Proof.
  intros MOVE CODE STACK; inversion MOVE; subst; simpl in CODE;
    try solve [repeat split; auto; intros id IN; reflexivity].
  - destruct (in_dec peq id protected) as [IN|NOTIN]; [discriminate|].
    repeat split; auto. intros other IN; rewrite PTree.gso; [reflexivity|].
    intro EQ; subst other; contradiction.
  - apply andb_true_iff in CODE as [L R]. repeat split; auto; intros id IN; reflexivity.
  - inversion STACK; subst; repeat split; auto; intros id IN; reflexivity.
  - apply andb_true_iff in CODE as [L R]; destruct b; repeat split; auto; intros id IN; reflexivity.
Qed.

Section FINITE_FRAME.
Variable protected : list ident.
Variable source : statement.
Hypothesis SOURCE : frame_statement protected source = true.
Variable temps : bool.
Variable ge : genv.
Variable fn : function.
Variable outside : cont.
Variable locals : env.

Record framed_finite_cursor := FramedFiniteCursor {
  ff_code : statement;
  ff_stack : list statement;
  ff_temps : temp_env;
  ff_memory : mem;
  ff_code_frame : frame_statement protected ff_code = true;
  ff_stack_frame : Forall (fun s => frame_statement protected s = true) ff_stack
}.
Definition ff_state c := State fn (ff_code c) (region_cont (ff_stack c) outside)
  locals (ff_temps c) (ff_memory c).
Definition ff_rank c := state_weight
  (State fn (ff_code c) (region_cont (ff_stack c) Kstop) locals (ff_temps c) (ff_memory c)).
Definition ff_done c := match ff_code c, ff_stack c with
  | Sskip, [] => Some (ff_temps c, ff_memory c) | _, _ => None end.
Definition ff_step c next := fragment_step ge locals (ff_code c) (ff_stack c) (ff_temps c)
  (ff_memory c) (ff_code next) (ff_stack next) (ff_temps next) (ff_memory next).
Definition ff_completion c result := resumed_execution (adapter_entry temps) ge locals
  (ff_code c) (ff_stack c) (ff_temps c) (ff_memory c) (fst result) (snd result).

Lemma ff_sound c next : ff_step c next -> adapter_step temps ge (ff_state c) E0 (ff_state next).
Proof. unfold ff_step, ff_state; intro STEP; inversion STEP; subst; simpl; econstructor; eauto. Qed.
Lemma ff_active c next : ff_step c next -> ff_done c = None.
Proof.
  destruct c as [code stack le m CODE STACK]; unfold ff_step, ff_done; simpl;
    intro STEP; inversion STEP; reflexivity.
Qed.
Lemma ff_decreases c next : ff_step c next -> ff_rank next < ff_rank c.
Proof. unfold ff_step, ff_rank; intro STEP; eapply fragment_step_decreases; exact STEP. Qed.
Lemma ff_closed c events next_state : ff_done c = None ->
  adapter_step temps ge (ff_state c) events next_state ->
  exists next, events = E0 /\ next_state = ff_state next /\ ff_step c next.
Proof.
  destruct c as [code stack le m CODE STACK]; cbn [ff_state]; intros DONE STEP.
  assert (ACTIVE : code <> Sskip \/ stack <> []).
  { destruct code; try (left; discriminate). destruct stack; [discriminate DONE|right; discriminate]. }
  pose proof (frame_statement_finite protected code CODE) as FIN.
  assert (FSTACK : Forall (fun s => finite_statement s = true) stack)
    by (eapply Forall_impl; [intros s S; apply frame_statement_finite with protected; exact S|exact STACK]).
  destruct (@fragment_step_from_ambient (adapter_entry temps) ge locals fn code stack outside le m
    events next_state FIN FSTACK ACTIVE STEP) as [code' [stack' [le' [m' [TRACE [STATE MOVE]]]]]].
  destruct (@frame_statement_step protected ge locals code stack le m code' stack' le' m'
    MOVE CODE STACK) as [FRAME [CODE' STACK']].
  exists (@FramedFiniteCursor code' stack' le' m' CODE' STACK'); cbn; repeat split; auto.
Qed.
Lemma ff_prepend c next result : ff_step c next -> ff_completion next result -> ff_completion c result.
Proof. unfold ff_step, ff_completion; intros STEP RUN; eapply fragment_step_prepend; eauto. Qed.
Lemma ff_done_state c result : ff_done c = Some result -> ff_state c = progress_exit_state fn outside locals result.
Proof.
  destruct c as [code stack le m CODE STACK]; unfold ff_done; simpl;
    destruct code; destruct stack; try discriminate; intro DONE; inversion DONE; reflexivity.
Qed.
Lemma ff_done_completion c result : ff_done c = Some result -> ff_completion c result.
Proof.
  destruct c as [code stack le m CODE STACK]; unfold ff_done; simpl;
    destruct code; destruct stack; try discriminate; intro DONE; inversion DONE; subst; apply completed_execution.
Qed.
Definition framed_finite_protocol :=
  {| cursor := framed_finite_cursor; cursor_state := ff_state; cursor_rank := ff_rank;
     cursor_done := ff_done; cursor_completion := ff_completion; cursor_step := ff_step;
     cursor_step_sound := ff_sound; cursor_step_active := ff_active;
     cursor_step_decreases := ff_decreases; cursor_step_closed := ff_closed;
     cursor_completion_prepend := ff_prepend; cursor_done_state := ff_done_state;
     cursor_done_completion := ff_done_completion |}.
Definition framed_finite_entry : protocol_entry framed_finite_protocol (temp_env * mem)
  (fun input => State fn source outside locals (fst input) (snd input))
  (fun input result => exec_stmt (adapter_entry temps) ge locals (fst input) (snd input)
    source E0 (fst result) (snd result) Out_normal).
Proof.
  refine (@ProtocolEntry state event (temp_env * mem) (adapter_step temps ge)
    (progress_exit_state fn outside locals) framed_finite_protocol (temp_env * mem)
    _ _ (fun input => @FramedFiniteCursor source [] (fst input) (snd input) SOURCE (Forall_nil _)) _ _).
  - intros; reflexivity.
  - intros input result RUN; eapply initial_execution; exact RUN.
Defined.
End FINITE_FRAME.

Definition finite_framed_progress protected source (SOURCE : frame_statement protected source = true) :
  framed_progress source protected.
Proof.
  refine {| framed_quiet := finite_statement_quiet source (frame_statement_finite protected source SOURCE);
    framed_protocol := fun temps ge fn outside locals => @framed_finite_protocol protected temps ge fn outside locals;
    framed_entry := fun temps ge fn outside locals => @framed_finite_entry protected source SOURCE temps ge fn outside locals;
    framed_view := fun temps ge fn outside locals c => (ff_temps c, ff_memory c);
    framed_bound := statement_weight source |}.
  - intros; repeat eexists; reflexivity.
  - intros temps ge fn outside locals [le m]; reflexivity.
  - intros; change (statement_weight source + 0 <= statement_weight source); lia.
  - intros temps ge fn outside locals [code stack le m CODE STACK] result DONE;
      cbn [cursor_done framed_finite_protocol ff_done] in DONE;
      destruct code; destruct stack; try discriminate; reflexivity.
  - intros temps ge fn outside locals c next STEP.
    exact (proj1 (@frame_statement_step protected ge locals _ _ _ _ _ _ _ _ STEP
      (ff_code_frame c) (ff_stack_frame c))).
Defined.

Print Assumptions finite_framed_progress.
