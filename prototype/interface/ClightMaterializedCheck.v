From Stdlib Require Import List Bool.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightLoopSyntax.
From GuardInterface Require Import GuardInterface ClightReadonlyRewrite ClightPrivateScan
  ClightPrivateScanSafety ClightQuietDeterminacy.
Set Implicit Arguments.

(** A normal, memory-read-only check may write and read its private result.
    This is separate from the rejecting-break scan representation. *)
Fixpoint materialized_body_check body := match body with
| Sskip | Sset _ _ | Sbreak => true
| Ssequence first second | Sifthenelse _ first second | Sloop first second =>
    materialized_body_check first && materialized_body_check second
| _ => false end.

Lemma materialized_body_check_sound body :
  materialized_body_check body=true -> private_scan_statement body.
Proof.
  induction body; cbn; try discriminate; intros CHECK; try constructor.
  all: apply andb_true_iff in CHECK as [FIRST SECOND]; auto.
Qed.

Record materialized_check := MaterializedCheck {
  materialized_body : statement;
  materialized_condition : expr;
  materialized_supported : private_scan_statement materialized_body;
  materialized_normal : normal_statement materialized_body=true
}.

Definition describe_materialized_check (body : statement) (condition : expr) : option materialized_check.
Proof.
  destruct (Bool.bool_dec (materialized_body_check body) true) as [SUPPORTED|]; [|exact None].
  destruct (Bool.bool_dec (normal_statement body) true) as [NORMAL|]; [|exact None].
  exact (Some (@MaterializedCheck body condition (@materialized_body_check_sound body SUPPORTED) NORMAL)).
Defined.

Lemma describe_materialized_check_exact body condition test :
  describe_materialized_check body condition=Some test ->
  materialized_body test=body /\ materialized_condition test=condition.
Proof.
  unfold describe_materialized_check; destruct (Bool.bool_dec (materialized_body_check body) true); [|discriminate].
  destruct (Bool.bool_dec (normal_statement body) true); [|discriminate]; intro SAME; inversion SAME; auto.
Qed.

Definition materialized_safe fe test entry :=
  private_scan_safe fe (entry_ge entry) (entry_env entry)
    (materialized_body test) (entry_temps entry) (entry_memory entry) /\
  forall trace after final,
    exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
      (materialized_body test) trace after final Out_normal ->
    exists accepted, expression_test (materialized_condition test)
      (Entry (entry_ge entry) (entry_env entry) after final) accepted.

Definition materialized_checks fe test entry accepted checked :=
  exists after,
    exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
      (materialized_body test) E0 after (entry_memory entry) Out_normal /\
    expression_test (materialized_condition test)
      (Entry (entry_ge entry) (entry_env entry) after (entry_memory entry)) accepted /\
    checked=Entry (entry_ge entry) (entry_env entry) after (entry_memory entry).

Definition materialized_select test yes no :=
  Ssequence (materialized_body test) (Sifthenelse (materialized_condition test) yes no).

Theorem materialized_select_execution_exact fe ge locals temps memory test yes no trace after final outcome :
  exec_stmt fe ge locals temps memory (materialized_select test yes no) trace after final outcome <->
  exists accepted middle,
    exec_stmt fe ge locals temps memory (materialized_body test) E0 middle memory Out_normal /\
    expression_test (materialized_condition test) (Entry ge locals middle memory) accepted /\
    exec_stmt fe ge locals middle memory (if accepted then yes else no) trace after final outcome.
Proof.
  split.
  - intro RUN; unfold materialized_select in RUN; inversion RUN; subst.
    + match goal with CHECK : exec_stmt _ _ _ _ _ (materialized_body test) _ _ _ _ |- _ =>
        destruct (@private_scan_completed_shape _ _ _ _ _ _ _ _ _ _ CHECK (materialized_supported test))
          as [TRACE [MEMORY _]]; subst end.
      match goal with CHOICE : exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) _ _ _ _ |- _ => inversion CHOICE; subst end.
      eexists _,_; split; [eassumption|split; [exists v1; split; eassumption|eassumption]].
    + match goal with CHECK : exec_stmt _ _ _ _ _ (materialized_body test) _ _ _ _ |- _ =>
        pose proof (@normal_statement_execution _ _ _ _ (materialized_normal test) _ _ _ _ _ _ CHECK) as NORMAL;
        subst end; contradiction.
  - intros [accepted [middle [CHECK [[value [EVAL BOOL]] BRANCH]]]].
    unfold materialized_select; eapply exec_Sseq_1 with (t1:=E0) (t2:=trace); [exact CHECK|].
    eapply exec_Sifthenelse; eassumption.
Qed.

Definition materialized_host
  (fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop)
  {O : Type} (observe : fragment_observation -> O -> Prop) :
  guard_host clight_entry.
Proof.
  refine {| code:=statement; check:=materialized_check; observation:=O;
    runs:=readonly_clight_runs fe observe; checks:=materialized_checks fe;
    check_safe:=materialized_safe fe; select:=materialized_select |}.
  intros test yes no entry observed; split.
  - intros [raw [RUN OBSERVE]]; unfold clight_fragment_run in RUN.
    apply materialized_select_execution_exact in RUN as [accepted [middle [CHECK [TEST BRANCH]]]].
    exists accepted,(Entry (entry_ge entry) (entry_env entry) middle (entry_memory entry)); split.
    + exists middle; auto.
    + exists raw; split; [exact BRANCH|exact OBSERVE].
  - intros [accepted [checked [[middle [CHECK [TEST SAME]]] [raw [BRANCH OBSERVE]]]]]; subst checked.
    exists raw; split; [|exact OBSERVE].
    unfold clight_fragment_run in *; cbn [entry_ge entry_env entry_temps entry_memory] in BRANCH.
    apply materialized_select_execution_exact; exists accepted,middle; auto.
Defined.

Theorem materialized_safe_available fe test entry : materialized_safe fe test entry ->
  exists accepted checked, materialized_checks fe test entry accepted checked.
Proof.
  intros [SAFE TEST].
  destruct (@private_scan_safe_execution fe (entry_ge entry) (entry_env entry) _ _ _ SAFE (materialized_supported test))
    as [after [outcome [RUN _]]].
  pose proof (@normal_statement_execution _ _ _ _ (materialized_normal test) _ _ _ _ _ _ RUN) as NORMAL; subst outcome.
  destruct (TEST _ _ _ RUN) as [accepted CHECK].
  exists accepted,(Entry (entry_ge entry) (entry_env entry) after (entry_memory entry)); exists after; auto.
Qed.

Theorem materialized_execution_safe fe test entry after accepted :
  exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
    (materialized_body test) E0 after (entry_memory entry) Out_normal ->
  expression_test (materialized_condition test)
    (Entry (entry_ge entry) (entry_env entry) after (entry_memory entry)) accepted ->
  materialized_safe fe test entry.
Proof.
  intros RUN TEST; split.
  - eapply completed_private_scan_safe; [exact RUN|apply materialized_supported].
  - intros trace other final OTHER.
    destruct (@quiet_execution_determinate _ _ _ _ _ _ _ _ _ _ RUN
      (private_scan_quiet (materialized_supported test)) _ _ _ _ OTHER) as [_ [TEMPS [MEMORY _]]].
    subst other final; exists accepted; exact TEST.
Qed.

Print Assumptions materialized_body_check_sound.
Print Assumptions describe_materialized_check_exact.
Print Assumptions materialized_select_execution_exact.
Print Assumptions materialized_host.
Print Assumptions materialized_safe_available.
Print Assumptions materialized_execution_safe.
