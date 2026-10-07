From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightNoWrap ClightLoopSyntax ClightRegionProgress CompCertMemoryActions.
From GuardInterface Require Import ClightExpressionBodyPrefix ClightObservedHeaderPrefix ClightStorePermissions.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A prefix stores readiness only at its own entry. Narrowing that predicate
    to the fixed entry lets clients supply HEADER there, rather than prove it
    at unrelated entries with unrelated cached words. *)
Lemma expression_body_prefix_ready_change fe row cache bound body stable first second observations index entry :
  expression_body_prefix fe row cache bound body stable first observations index entry ->
  second entry ->
  expression_body_prefix fe row cache bound body stable second observations index entry.
Proof. intros [_ REST] READY; split; assumption. Qed.

Section ENTRY.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variables row cache : ident.
Variable bound : expr.
Variable body : statement.
Variable stable : list ident.
Variable ready : clight_entry -> Prop.
Variable observations : clight_entry -> list(memory_location*val).
Variable entry : clight_entry.
Hypothesis TYPE : typeof bound=type_int32s.
Hypotheses (NORMAL : normal_statement body=true) (QUIET : quiet_statement body=true).
Hypothesis HEADER : forall index current memory,
  ready entry -> 0<=index<=Int.signed(temp_word cache(entry_temps entry)) ->
  current!row=Some(Vint(Int.repr index)) -> temp_agree stable(entry_temps entry) current ->
  header_observations_match(observations entry) memory ->
  eval_expr(entry_ge entry)(entry_env entry) current memory bound(Vint(temp_word cache(entry_temps entry))).

Lemma expression_body_prefix_fixed index :
  expression_body_prefix fe row cache bound body stable ready observations index entry ->
  expression_body_prefix fe row cache bound body stable
    (fun origin=>ready origin /\ origin=entry) observations index entry.
Proof. intro PREFIX; eapply expression_body_prefix_ready_change; [exact PREFIX|split; [exact(proj1 PREFIX)|reflexivity]]. Qed.

Theorem expression_body_prefix_receipt_at index :
  expression_body_prefix fe row cache bound body stable ready observations index entry ->
  index<Int.signed(temp_word cache(entry_temps entry)) -> exists current memory after final,
    current!row=Some(Vint(Int.repr index)) /\ temp_agree stable(entry_temps entry) current /\
    header_observations_match(observations entry) memory /\ memory_accesses_back(entry_memory entry) memory /\
    exec_stmt fe(entry_ge entry)(entry_env entry) current memory body E0 after final Out_normal.
Proof.
  intros PREFIX ACTIVE.
  eapply expression_body_prefix_receipt with(ready:=fun origin=>ready origin /\ origin=entry);
    [exact TYPE|exact NORMAL|exact QUIET| |apply expression_body_prefix_fixed; exact PREFIX|exact ACTIVE].
  intros origin index' current memory [READY SAME]; subst origin; eapply HEADER; eassumption.
Qed.

Theorem expression_body_prefix_advance_at written index :
  ~In row stable -> writes_only written body -> ~In row written ->
  (forall identifier,In identifier stable -> ~In identifier written) ->
  (forall ge locals current memory after final,
    exec_stmt fe ge locals current memory body E0 after final Out_normal -> memory_accesses_back memory final) ->
  expression_body_prefix fe row cache bound body stable ready observations index entry ->
  index<Int.signed(temp_word cache(entry_temps entry)) ->
  expression_body_preserved fe row body stable observations index entry ->
  expression_body_prefix fe row cache bound body stable ready observations(index+1) entry.
Proof.
  intros FRESH WRITES PRIVATE STABLE PERMISSIONS PREFIX ACTIVE PRESERVE.
  eapply expression_body_prefix_ready_change; [|exact(proj1 PREFIX)].
  eapply expression_body_prefix_advance with(written:=written)
    (ready:=fun origin=>ready origin /\ origin=entry);
    [exact TYPE|exact FRESH|exact NORMAL|exact QUIET|exact WRITES|exact PRIVATE|exact STABLE|
     exact PERMISSIONS| |apply expression_body_prefix_fixed; exact PREFIX|exact ACTIVE|exact PRESERVE].
  intros origin index' current memory [READY SAME]; subst origin; eapply HEADER; eassumption.
Qed.
End ENTRY.

Print Assumptions expression_body_prefix_ready_change.
Print Assumptions expression_body_prefix_receipt_at.
Print Assumptions expression_body_prefix_advance_at.
