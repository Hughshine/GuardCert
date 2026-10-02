From Stdlib Require Import List Arith Lia.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import SilentRegionProtocol ClightGuard ClightRegionProgress ClightFragmentProgress.
Set Implicit Arguments.
Local Open Scope nat_scope.

Section SEQUENCE.
Variables left right : statement.
Variable protected : list ident.
Variable F : framed_progress left protected.
Variable G : framed_progress right protected.
Variable temps : bool.
Variable ge : genv.
Variable fn : function.
Variable outside : cont.
Variable locals : env.
Let PL := framed_protocol F temps ge fn (Kseq right outside) locals.
Let PR := framed_protocol G temps ge fn outside locals.
Let EL := framed_entry F temps ge fn (Kseq right outside) locals.
Let ER := framed_entry G temps ge fn outside locals.
Let VL := framed_view F temps ge fn (Kseq right outside) locals.
Let VR := framed_view G temps ge fn outside locals.

Inductive sequence_cursor :=
| sq_start (input : temp_env * mem)
| sq_left (c : cursor PL)
| sq_right (c : cursor PR).
Definition sq_state c := match c with
  | sq_start input => State fn (Ssequence left right) outside locals (fst input) (snd input)
  | sq_left c => cursor_state PL c
  | sq_right c => cursor_state PR c end.
Definition sq_view c := match c with
  | sq_start input => input | sq_left c => VL c | sq_right c => VR c end.
Definition sq_rank c := match c with
  | sq_start _ => framed_bound F + framed_bound G + 2
  | sq_left c => framed_bound G + cursor_rank PL c + 1
  | sq_right c => cursor_rank PR c end.
Definition sq_done c := match c with
  | sq_right c => cursor_done PR c | _ => None end.
Definition sq_completion c result := match c with
  | sq_start input => exec_stmt (adapter_entry temps) ge locals (fst input) (snd input)
      (Ssequence left right) E0 (fst result) (snd result) Out_normal
  | sq_left c => exists middle, cursor_completion PL c middle /\
      exec_stmt (adapter_entry temps) ge locals (fst middle) (snd middle)
        right E0 (fst result) (snd result) Out_normal
  | sq_right c => cursor_completion PR c result end.
Inductive sq_step : sequence_cursor -> sequence_cursor -> Prop :=
| sq_step_start input : sq_step (sq_start input) (sq_left (begin_cursor EL input))
| sq_step_left c next : cursor_step PL c next -> sq_step (sq_left c) (sq_left next)
| sq_step_middle c result : cursor_done PL c = Some result ->
    sq_step (sq_left c) (sq_right (begin_cursor ER result))
| sq_step_right c next : cursor_step PR c next -> sq_step (sq_right c) (sq_right next).

Lemma sq_sound c next : sq_step c next -> adapter_step temps ge (sq_state c) E0 (sq_state next).
Proof.
  intro MOVE; inversion MOVE; subst; cbn [sq_state].
  - rewrite (begin_state EL); constructor.
  - apply (cursor_step_sound PL); assumption.
  - rewrite (cursor_done_state PL _ H), (begin_state ER); constructor.
  - apply (cursor_step_sound PR); assumption.
Qed.
Lemma sq_active c next : sq_step c next -> sq_done c = None.
Proof.
  intro MOVE; inversion MOVE; subst; cbn [sq_done]; try reflexivity.
  eapply cursor_step_active; eassumption.
Qed.
Lemma sq_decreases c next : sq_step c next -> sq_rank next < sq_rank c.
Proof.
  intro MOVE; inversion MOVE; subst; cbn [sq_rank].
  - pose proof (framed_begin_bound F temps ge fn (Kseq right outside) locals input).
    unfold PL, EL in *; lia.
  - pose proof (cursor_step_decreases PL _ _ H); lia.
  - pose proof (framed_done_rank F temps ge fn (Kseq right outside) locals _ H).
    pose proof (framed_begin_bound G temps ge fn outside locals result).
    unfold PL, PR, ER in *; lia.
  - eapply cursor_step_decreases; eassumption.
Qed.
Lemma sq_closed c events next_state : sq_done c = None ->
  adapter_step temps ge (sq_state c) events next_state ->
  exists next, events = E0 /\ next_state = sq_state next /\ sq_step c next.
Proof.
  destruct c as [input|c|c]; cbn [sq_done sq_state]; intros DONE STEP.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (sq_left (begin_cursor EL input)); split; [reflexivity|split].
    + cbn [sq_state]; rewrite (begin_state EL); reflexivity.
    + constructor.
  - destruct (cursor_done PL c) as [result|] eqn:LEFT_DONE.
    + rewrite (cursor_done_state PL c LEFT_DONE) in STEP.
      inversion STEP; subst; try contradiction;
        try match goal with BAD : is_call_cont (Kseq _ _) |- _ => contradiction end.
      exists (sq_right (begin_cursor ER result)); split; [reflexivity|split].
      * cbn [sq_state]; rewrite (begin_state ER); reflexivity.
      * constructor; exact LEFT_DONE.
    + destruct (cursor_step_closed PL c _ _ LEFT_DONE STEP) as [next [TRACE [STATE MOVE]]].
      exists (sq_left next); repeat split; auto; constructor; exact MOVE.
  - destruct (cursor_step_closed PR c _ _ DONE STEP) as [next [TRACE [STATE MOVE]]].
    exists (sq_right next); repeat split; auto; constructor; exact MOVE.
Qed.
Lemma sq_prepend c next result : sq_step c next -> sq_completion next result -> sq_completion c result.
Proof.
  intros MOVE RUN; inversion MOVE; subst; cbn [sq_completion] in RUN |- *.
  - destruct RUN as [middle [L R]]. apply (begin_completion EL) in L.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact L|exact R].
  - destruct RUN as [middle [L R]]; exists middle; split; [|exact R].
    eapply cursor_completion_prepend; eauto.
  - exists result0; split; [eapply cursor_done_completion; exact H|].
    apply (begin_completion ER); exact RUN.
  - eapply cursor_completion_prepend; eauto.
Qed.
Lemma sq_done_state c result : sq_done c = Some result ->
  sq_state c = progress_exit_state fn outside locals result.
Proof. destruct c; cbn [sq_done sq_state]; try discriminate; apply cursor_done_state. Qed.
Lemma sq_done_completion c result : sq_done c = Some result -> sq_completion c result.
Proof. destruct c; cbn [sq_done sq_completion]; try discriminate; apply cursor_done_completion. Qed.
Definition sequence_protocol :=
  {| cursor := sequence_cursor; cursor_state := sq_state; cursor_rank := sq_rank;
     cursor_done := sq_done; cursor_completion := sq_completion; cursor_step := sq_step;
     cursor_step_sound := sq_sound; cursor_step_active := sq_active;
     cursor_step_decreases := sq_decreases; cursor_step_closed := sq_closed;
     cursor_completion_prepend := sq_prepend; cursor_done_state := sq_done_state;
     cursor_done_completion := sq_done_completion |}.
Definition sequence_entry : protocol_entry sequence_protocol (temp_env * mem)
  (fun input => State fn (Ssequence left right) outside locals (fst input) (snd input))
  (fun input result => exec_stmt (adapter_entry temps) ge locals (fst input) (snd input)
    (Ssequence left right) E0 (fst result) (snd result) Out_normal).
Proof.
  refine (@ProtocolEntry state event (temp_env * mem) (adapter_step temps ge)
    (progress_exit_state fn outside locals) sequence_protocol (temp_env * mem) _ _ sq_start _ _);
    intros; auto.
Defined.

Lemma sq_frame c next : sq_step c next ->
  preserves_temporaries protected (fst (sq_view c)) (fst (sq_view next)).
Proof.
  intro MOVE; inversion MOVE; subst; cbn [sq_view].
  - unfold VL, EL; rewrite framed_begin_view; intros id IN; reflexivity.
  - exact (framed_step_frame F temps ge fn (Kseq right outside) locals _ _ H).
  - unfold VL, VR, ER. rewrite (framed_done_view F temps ge fn (Kseq right outside) locals _ H),
      framed_begin_view. intros id IN; reflexivity.
  - exact (framed_step_frame G temps ge fn outside locals _ _ H).
Qed.
End SEQUENCE.

Definition sequence_framed_progress left right protected
  (F : framed_progress left protected) (G : framed_progress right protected) :
  framed_progress (Ssequence left right) protected.
Proof.
  refine {| framed_quiet := _;
    framed_protocol := fun temps ge fn outside locals => @sequence_protocol left right protected F G temps ge fn outside locals;
    framed_entry := fun temps ge fn outside locals => @sequence_entry left right protected F G temps ge fn outside locals;
    framed_view := fun temps ge fn outside locals => @sq_view left right protected F G temps ge fn outside locals;
    framed_bound := framed_bound F + framed_bound G + 2 |}.
  - cbn [quiet_statement]; rewrite (framed_quiet F), (framed_quiet G); reflexivity.
  - intros temps ge fn outside locals [input|c|c]; cbn [cursor_state sequence_protocol sq_state sq_view].
    + repeat eexists; reflexivity.
    + apply (framed_shape F).
    + apply (framed_shape G).
  - intros; reflexivity.
  - intros; cbn [cursor_rank sequence_protocol begin_cursor sequence_entry sq_rank]; lia.
  - intros temps ge fn outside locals [input|c|c] result DONE; cbn [cursor_done sequence_protocol sq_done] in DONE;
      try discriminate. apply (framed_done_rank G temps ge fn outside locals c DONE).
  - intros; apply sq_frame; assumption.
Defined.

Definition framed_region_progress source protected (F : framed_progress source protected)
  (ACTIVE : forall temps ge fn outside locals input,
    cursor_done (framed_protocol F temps ge fn outside locals)
      (begin_cursor (framed_entry F temps ge fn outside locals) input) = None) : region_progress source.
Proof.
  refine {| progress_label_free := quiet_statement_label_free source (framed_quiet F);
    progress_protocol := framed_protocol F; progress_entry := framed_entry F;
    progress_initial_active := ACTIVE |}.
  - intros temps ge fn outside locals c; destruct (framed_shape F temps ge fn outside locals c) as [code [k SHAPE]].
    exists code, k, (fst (framed_view F temps ge fn outside locals c)),
      (snd (framed_view F temps ge fn outside locals c)); exact SHAPE.
  - intros; eapply quiet_execution_preserved; [eassumption|eassumption|exact (framed_quiet F)].
Defined.

Definition sequence_region_progress left right protected
  (F : framed_progress left protected) (G : framed_progress right protected) :
  region_progress (Ssequence left right).
Proof. apply (framed_region_progress (sequence_framed_progress F G)); intros; reflexivity. Defined.

Print Assumptions sequence_framed_progress.
Print Assumptions sequence_region_progress.
