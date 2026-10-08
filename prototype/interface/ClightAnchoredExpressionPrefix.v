(** Instantiate prefix services with facts at the actual observation anchor.
    Opening a nested child does not require header laws for unrelated states. *)
From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightNoWrap ClightLoopSyntax
  ClightRegionProgress CompCertMemoryActions.
From GuardInterface Require Import ClightExpressionBodyPrefix ClightObservedHeaderPrefix ClightStorePermissions.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma expression_prefix_ready_transport fe row cache bound body stable ready next observations index entry :
  (ready entry -> next entry) ->
  expression_body_prefix fe row cache bound body stable ready observations index entry ->
  expression_body_prefix fe row cache bound body stable next observations index entry.
Proof. intros CHANGE [READY REST]; split; [apply CHANGE; exact READY|exact REST]. Qed.

Section LOCAL.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variables row cache : ident.
Variable bound : expr.
Variable body : statement.
Variable stable : list ident.
Variable ready : clight_entry -> Prop.
Variable observations : clight_entry -> list (memory_location * val).
Variable entry : clight_entry.
Hypothesis TYPE : typeof bound=type_int32s.
Hypotheses (NORMAL : normal_statement body=true) (QUIET : quiet_statement body=true).
Hypothesis HEADER : forall index current memory,
  ready entry -> 0<=index<=Int.signed(temp_word cache(entry_temps entry)) ->
  current!row=Some(Vint(Int.repr index)) -> temp_agree stable(entry_temps entry) current ->
  header_observations_match(observations entry) memory ->
  eval_expr(entry_ge entry)(entry_env entry) current memory bound (Vint(temp_word cache(entry_temps entry))).

Theorem expression_prefix_local_receipt index :
  expression_body_prefix fe row cache bound body stable ready observations index entry ->
  index<Int.signed(temp_word cache(entry_temps entry)) ->
  exists current memory after final,
    current!row=Some(Vint(Int.repr index)) /\ temp_agree stable(entry_temps entry) current /\
    header_observations_match(observations entry) memory /\ memory_accesses_back(entry_memory entry) memory /\
    exec_stmt fe(entry_ge entry)(entry_env entry) current memory body E0 after final Out_normal.
Proof.
  intros PREFIX ACTIVE; eapply expression_body_prefix_receipt with
    (ready:=fun state=>state=entry /\ ready state); try eassumption.
  - intros state index' current memory [SAME READY] RANGE ROW FRAME OBSERVED;
      subst state; eapply HEADER; [exact READY|exact RANGE|exact ROW|exact FRAME|exact OBSERVED].
  - eapply expression_prefix_ready_transport; [|exact PREFIX]; intros READY; split; [reflexivity|exact READY].
Qed.

Variable written : list ident.
Hypothesis ROW_PRIVATE : ~In row stable.
Hypothesis WRITES : writes_only written body.
Hypothesis ROW_UNWRITTEN : ~In row written.
Hypothesis STABLE_UNWRITTEN : forall id, In id stable -> ~In id written.
Hypothesis PERMISSIONS : forall ge locals current memory after final,
  exec_stmt fe ge locals current memory body E0 after final Out_normal -> memory_accesses_back memory final.

Theorem expression_prefix_local_advance index :
  expression_body_prefix fe row cache bound body stable ready observations index entry ->
  index<Int.signed(temp_word cache(entry_temps entry)) ->
  expression_body_preserved fe row body stable observations index entry ->
  expression_body_prefix fe row cache bound body stable ready observations (index+1) entry.
Proof.
  intros PREFIX ACTIVE PRESERVE.
  eapply expression_prefix_ready_transport with (ready:=fun state=>state=entry /\ ready state);
    [intros [_ READY]; exact READY|].
  eapply expression_body_prefix_advance with (written:=written);
    try exact TYPE; try exact ROW_PRIVATE; try exact NORMAL; try exact QUIET;
    try exact WRITES; try exact ROW_UNWRITTEN; try exact STABLE_UNWRITTEN;
    try exact PERMISSIONS; try exact ACTIVE; try exact PRESERVE.
  - intros state index' current memory [SAME READY] RANGE ROW FRAME OBSERVED;
      subst state; eapply HEADER; [exact READY|exact RANGE|exact ROW|exact FRAME|exact OBSERVED].
  - eapply expression_prefix_ready_transport; [|exact PREFIX]; intros READY; split; [reflexivity|exact READY].
Qed.
End LOCAL.

Print Assumptions expression_prefix_ready_transport.
Print Assumptions expression_prefix_local_receipt.
Print Assumptions expression_prefix_local_advance.
