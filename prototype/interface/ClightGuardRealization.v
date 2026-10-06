From Stdlib Require Import List Bool.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events Smallstep.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightTempFrame ClightTempFootprint ClightProjectedExecution.
From GuardInterface Require Import ClightSharedGuard.
Import ListNotations.
Set Implicit Arguments.

(** A language implementation of finite dispatch, independent of whether the
    chosen branch terminates. The logical readonly check still uses the original
    entry; only the implementation may update declared private temporaries. *)
Record clight_guard_realization (live : list ident) tree (yes no : statement) := {
  realization_code : statement;
  realization_private : list ident;
  realization_entry : bool -> temp_env -> temp_env;
  realization_fresh : forall id, In id realization_private ->
    ~ In id (statement_temps yes ++ statement_temps no ++ live);
  realization_frame : forall accepted le id, ~ In id realization_private ->
    (realization_entry accepted le) ! id = le ! id;
  realization_dispatch : forall temps ge fn outside locals le m accepted,
    decision_run (Entry ge locals le m) tree accepted ->
    star (adapter_step temps) ge
      (State fn realization_code outside locals le m) E0
      (State fn (if accepted then yes else no) outside locals
        (realization_entry accepted le) m)
}.

Lemma realization_entry_agree live tree yes no
  (R : clight_guard_realization live tree yes no) accepted le :
  temp_agree (statement_temps yes ++ statement_temps no ++ live)
    le (realization_entry R accepted le).
Proof.
  intros id IN; apply realization_frame; intro PRIVATE.
  exact (realization_fresh R id PRIVATE IN).
Qed.

Definition direct_guard_realization live tree yes no :
  clight_guard_realization live tree yes no.
Proof.
  refine {| realization_code := tree_statement tree yes no;
    realization_private := []; realization_entry := fun _ le => le |}.
  - intros id IN; contradiction.
  - reflexivity.
  - intros; apply decision_dispatch; assumption.
Defined.

Lemma shared_guard_dispatch temps ge fn outside locals le m tree result yes no accepted :
  decision_run (Entry ge locals le m) tree accepted ->
  star (adapter_step temps) ge
    (State fn (shared_guard_statement tree result yes no) outside locals le m) E0
    (State fn (if accepted then yes else no) outside locals
      (PTree.set result (Vint (shared_guard_word accepted)) le) m).
Proof.
  intro CHECK; unfold shared_guard_statement, shared_guard_code.
  eapply star_step; [unfold adapter_step; apply step_seq | |reflexivity].
  eapply star_trans; [apply decision_dispatch; exact CHECK | |reflexivity].
  assert (SET : adapter_step temps ge
    (State fn (if accepted then Sset result (Econst_int Int.one type_int32s)
      else Sset result (Econst_int Int.zero type_int32s))
      (Kseq (Sifthenelse (shared_guard_choice result) yes no) outside) locals le m) E0
    (State fn Sskip (Kseq (Sifthenelse (shared_guard_choice result) yes no) outside)
      locals (PTree.set result (Vint (shared_guard_word accepted)) le) m)).
  { destruct accepted; unfold adapter_step; apply step_set; constructor. }
  eapply star_step; [exact SET | |reflexivity].
  eapply star_step; [unfold adapter_step; apply step_skip_seq | |reflexivity].
  destruct (@shared_guard_choice_test ge locals
    (PTree.set result (Vint (shared_guard_word accepted)) le) m result accepted (PTree.gss _ _ _))
    as [value [EVAL BOOL]].
  apply star_one; unfold adapter_step; eapply step_ifthenelse; eassumption.
Qed.

Definition shared_guard_realization live tree yes no result
  (FRESH : ~ In result (statement_temps yes ++ statement_temps no ++ live)) :
  clight_guard_realization live tree yes no.
Proof.
  refine {| realization_code := shared_guard_statement tree result yes no;
    realization_private := [result];
    realization_entry := fun accepted le => PTree.set result (Vint (shared_guard_word accepted)) le |}.
  - intros id [SAME|FALSE]; [subst id; exact FRESH | contradiction].
  - intros accepted le id PRIVATE; apply PTree.gso.
    intro SAME; subst id; apply PRIVATE; left; reflexivity.
  - intros; apply shared_guard_dispatch; assumption.
Defined.

(** Completed-run installation is an additional adapter obligation. The
    dispatch certificate above does not acquire a termination assumption. *)
Record clight_normal_realization (live : list ident) tree (yes no : statement) := {
  normal_realization : clight_guard_realization live tree yes no;
  normal_branch_transport : forall fe ge locals le m (accepted : bool) after final,
    exec_stmt fe ge locals le m (if accepted then yes else no) E0 after final Out_normal ->
    exists target_after,
      exec_stmt fe ge locals (realization_entry normal_realization accepted le) m
        (if accepted then yes else no) E0 target_after final Out_normal /\
      temp_agree live after target_after
}.

Definition direct_normal_realization live tree yes no :
  clight_normal_realization live tree yes no.
Proof.
  refine {| normal_realization := direct_guard_realization live tree yes no |}.
  intros fe ge locals le m accepted after final RUN.
  exists after; split; [exact RUN | apply temp_agree_refl].
Defined.

Definition shared_normal_realization live tree yes no result yes_writes no_writes
  (YES : writes_only yes_writes yes) (NO : writes_only no_writes no)
  (FRESH : ~ In result (statement_temps yes ++ statement_temps no ++ live)) :
  clight_normal_realization live tree yes no.
Proof.
  refine {| normal_realization := shared_guard_realization live tree yes no result FRESH |}.
  intros fe ge locals le m accepted after final RUN.
  set (chosen := if accepted then yes else no).
  assert (WRITES : writes_only (if accepted then yes_writes else no_writes) chosen).
  { unfold chosen; destruct accepted; assumption. }
  assert (PRIVATE : ~ In result (statement_temps chosen ++ live)).
  { unfold chosen; destruct accepted; repeat rewrite in_app_iff in *; tauto. }
  destruct (@structured_execution_temp_transport fe ge locals le m chosen E0 after final
    Out_normal RUN (statement_temps chosen ++ live)
    (PTree.set result (Vint (shared_guard_word accepted)) le)
    (if accepted then yes_writes else no_writes) WRITES
    ltac:(unfold statement_scope; intros id IN; apply in_or_app; left; exact IN)
    (@temp_agree_set (statement_temps chosen ++ live) le result
      (Vint (shared_guard_word accepted)) PRIVATE)) as [exit [RUN' PUBLIC]].
  exists exit; split; [exact RUN' |].
  eapply temp_agree_weaken; [|exact PUBLIC].
  intros id IN; apply in_or_app; right; exact IN.
Defined.

Theorem realized_guard_normal_steps live tree yes no
  (R : clight_normal_realization live tree yes no)
  temps (p : Clight.program) fn outside locals le m accepted after final :
  decision_run (Entry (Clight.globalenv p) locals le m) tree accepted ->
  exec_stmt (adapter_entry temps) (Clight.globalenv p) locals le m
    (if accepted then yes else no) E0 after final Out_normal ->
  exists target_after,
    star (adapter_step temps) (Clight.globalenv p)
      (State fn (realization_code (normal_realization R)) outside locals le m) E0
      (State fn Sskip outside locals target_after final) /\
    temp_agree live after target_after.
Proof.
  intros CHECK LEAF.
  destruct (@normal_branch_transport live tree yes no R (adapter_entry temps)
    (Clight.globalenv p) locals le m accepted after final LEAF) as [exit [TRANSPORTED PUBLIC]].
  destruct (exec_stmt_steps (adapter_entry temps) p _ _ _ _ _ _ _ _ TRANSPORTED fn outside)
    as [next [STEPS EXIT]].
  inversion EXIT; subst next; exists exit; split; [|exact PUBLIC].
  eapply star_trans; [apply realization_dispatch; exact CHECK |exact STEPS|reflexivity].
Qed.

Print Assumptions realization_entry_agree.
Print Assumptions shared_guard_dispatch.
Print Assumptions shared_normal_realization.
Print Assumptions realized_guard_normal_steps.
