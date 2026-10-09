From Stdlib Require Import List Bool Arith ZArith.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightLoopSyntax ClightTempFrame ClightRegionProgress.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryLongControl GuardMemoryLongLoopControl
  GuardMemoryLongHeaderLicense GuardMemoryLongRawLoadedProgress GuardMemoryLongLoopSettle
  GuardMemoryDoubleMatmulNest GuardMemoryDoubleInitializedNestData.
Import ListNotations.
Set Implicit Arguments.

(** Each axis keeps its own actual loaded global header. Counts and blocks are
    execution receipts, not compile-time substitutions for these expressions. *)
Definition double_rectangular_axes := list (ident*ident).
Definition double_rectangular_iterators (axes : double_rectangular_axes) := map fst axes.
Fixpoint double_rectangular_nest_code (axes : double_rectangular_axes) body : statement :=
  match axes with
  | [] => body
  | (iterator,header)::rest => memory_long_initialized_loop iterator
      (memory_global_long_condition iterator header) (double_rectangular_nest_code rest body)
  end.
Fixpoint double_rectangular_raw_nest_code (axes : double_rectangular_axes) body : statement :=
  match axes with
  | [] => Ssequence Sskip body
  | (iterator,header)::rest => long_raw_initialized_loop iterator
      (Evar header memory_long_type) (double_rectangular_raw_nest_code rest body)
  end.
Lemma double_rectangular_nest_quiet axes body : quiet_statement body=true ->
  quiet_statement (double_rectangular_nest_code axes body)=true.
Proof.
  intro BODY; induction axes as [|[iterator header] rest IH]; cbn [double_rectangular_nest_code]; [exact BODY|].
  unfold memory_long_initialized_loop,memory_long_frontend_loop; cbn [quiet_statement]; rewrite IH; reflexivity.
Qed.
Lemma double_rectangular_nest_normal axes body :
  (exists target rhs, body=Sassign target rhs) -> normal_statement (double_rectangular_nest_code axes body)=true.
Proof.
  intros [target [rhs BODY]]; destruct axes as [|[iterator header] rest]; cbn [double_rectangular_nest_code];
    rewrite ?BODY; [reflexivity|].
  unfold memory_long_initialized_loop,memory_long_frontend_loop; cbn [normal_statement quiet_statement].
  rewrite double_rectangular_nest_quiet by reflexivity; reflexivity.
Qed.
Lemma double_rectangular_nest_writes axes body : (exists target rhs, body=Sassign target rhs) ->
  writes_only (double_rectangular_iterators axes) (double_rectangular_nest_code axes body).
Proof.
  intros [target [rhs BODY]]; induction axes as [|[iterator header] rest IH];
    cbn [double_rectangular_nest_code double_rectangular_iterators map fst]; [rewrite BODY; constructor|].
  unfold memory_long_initialized_loop,memory_long_frontend_loop,memory_long_increment.
  apply writes_sequence; [constructor; cbn; auto|apply writes_loop].
  - apply writes_sequence.
    + apply writes_if; constructor.
    + eapply writes_only_weaken; [intros key MEMBER; right; exact MEMBER|exact IH].
  - constructor; cbn; auto.
Qed.

(** The innermost public iterator is untouched after the first empty axis.
    Independent counts require distinct words, so use a fixed assignment list. *)
Fixpoint double_rectangular_exit_assignments (iterators : list ident) (counts : list nat) : list (ident*val) :=
  match iterators,counts with
  | iterator::rest,count::tail =>
      (iterator,Vlong (Int64.repr (Z.of_nat count)))::
      (match count with O=>[] | S _=>double_rectangular_exit_assignments rest tail end)
  | _,_ => [] end.
Fixpoint double_rectangular_set_assignments (assignments : list (ident*val)) (temps : temp_env) :=
  match assignments with []=>temps | (identifier,value)::rest =>
    PTree.set identifier value (double_rectangular_set_assignments rest temps) end.
Fixpoint double_rectangular_assignment_value (assignments : list (ident*val)) identifier : option val :=
  match assignments with []=>None | (key,value)::rest =>
    if peq identifier key then Some value else double_rectangular_assignment_value rest identifier end.
Lemma double_rectangular_set_assignments_lookup assignments temps identifier :
  (double_rectangular_set_assignments assignments temps) ! identifier=
  match double_rectangular_assignment_value assignments identifier with Some value=>Some value | None=>temps ! identifier end.
Proof.
  induction assignments as [|[key value] rest IH]; [reflexivity|].
  cbn [double_rectangular_set_assignments double_rectangular_assignment_value]; rewrite PTree.gsspec.
  destruct (peq identifier key); [reflexivity|exact IH].
Qed.
Lemma double_rectangular_set_assignments_idempotent assignments temps :
  double_rectangular_set_assignments assignments (double_rectangular_set_assignments assignments temps)=
  double_rectangular_set_assignments assignments temps.
Proof.
  apply PTree.extensionality; intro key; rewrite !double_rectangular_set_assignments_lookup.
  destruct (double_rectangular_assignment_value assignments key); reflexivity.
Qed.
Lemma double_rectangular_set_assignments_frame assignments temps key :
  ~ In key (map fst assignments) -> (double_rectangular_set_assignments assignments temps) ! key=temps ! key.
Proof.
  induction assignments as [|[identifier value] rest IH]; intro FRESH; [reflexivity|].
  cbn [double_rectangular_set_assignments]; rewrite PTree.gso by (intro SAME; subst; apply FRESH; cbn; auto).
  apply IH; intro MEMBER; apply FRESH; cbn; auto.
Qed.
Lemma double_rectangular_set_assignments_commute assignments temps iterator word :
  ~ In iterator (map fst assignments) ->
  double_rectangular_set_assignments assignments (PTree.set iterator word temps)=
  PTree.set iterator word (double_rectangular_set_assignments assignments temps).
Proof.
  induction assignments as [|[identifier value] rest IH]; intro FRESH; [reflexivity|].
  cbn [double_rectangular_set_assignments]; rewrite IH by (intro MEMBER; apply FRESH; cbn; auto).
  apply matmul_temp_set_commute; intro SAME; subst; apply FRESH; cbn; auto.
Qed.
Lemma double_rectangular_exit_assignments_subset iterators : forall counts key,
  In key (map fst (double_rectangular_exit_assignments iterators counts)) -> In key iterators.
Proof.
  induction iterators as [|iterator rest IH]; intros [|count counts] key MEMBER;
    cbn [double_rectangular_exit_assignments map fst] in MEMBER; try contradiction.
  cbn in MEMBER; destruct MEMBER as [SAME|MEMBER]; [subst; cbn; auto|].
  right; destruct count; [contradiction|eapply IH; exact MEMBER].
Qed.
Definition double_rectangular_nest_exit iterators counts temps :=
  double_rectangular_set_assignments (double_rectangular_exit_assignments iterators counts) temps.
Lemma double_rectangular_nest_exit_nil counts temps : double_rectangular_nest_exit [] counts temps=temps.
Proof. destruct counts; reflexivity. Qed.
Lemma double_rectangular_nest_exit_cons iterator rest count counts temps :
  double_rectangular_nest_exit (iterator::rest) (count::counts) temps=
  PTree.set iterator (Vlong (Int64.repr (Z.of_nat count)))
    (match count with O=>temps | S _=>double_rectangular_nest_exit rest counts temps end).
Proof. destruct count; reflexivity. Qed.
Lemma double_rectangular_nest_exit_idempotent iterators counts temps :
  double_rectangular_nest_exit iterators counts (double_rectangular_nest_exit iterators counts temps)=
  double_rectangular_nest_exit iterators counts temps.
Proof. apply double_rectangular_set_assignments_idempotent. Qed.
Lemma double_rectangular_nest_exit_frame iterators counts temps key :
  ~ In key iterators -> (double_rectangular_nest_exit iterators counts temps) ! key=temps ! key.
Proof.
  intro FRESH; apply double_rectangular_set_assignments_frame; intro MEMBER; apply FRESH;
    eapply double_rectangular_exit_assignments_subset; exact MEMBER.
Qed.
Lemma double_rectangular_nest_exit_commute iterators counts temps iterator word : ~ In iterator iterators ->
  double_rectangular_nest_exit iterators counts (PTree.set iterator word temps)=
  PTree.set iterator word (double_rectangular_nest_exit iterators counts temps).
Proof.
  intro FRESH; apply double_rectangular_set_assignments_commute; intro MEMBER; apply FRESH;
    eapply double_rectangular_exit_assignments_subset; exact MEMBER.
Qed.
Theorem double_rectangular_nest_settled_exit iterator rest count counts temps : ~ In iterator rest ->
  memory_long_settled_exit iterator (fun _ => double_rectangular_nest_exit rest counts) count 0
    (PTree.set iterator (Vlong Int64.zero) temps)=double_rectangular_nest_exit (iterator::rest) (count::counts) temps.
Proof.
  intro FRESH; destruct count as [|count]; [reflexivity|].
  rewrite (@memory_long_constant_settle_exit iterator (double_rectangular_nest_exit rest counts)
    ltac:(intro le; apply double_rectangular_nest_exit_idempotent)
    ltac:(intros le word; apply double_rectangular_nest_exit_commute; exact FRESH) count 0).
  rewrite Z.add_0_l,double_rectangular_nest_exit_commute by exact FRESH.
  rewrite PTree.set2,double_rectangular_nest_exit_cons; reflexivity.
Qed.

Print Assumptions double_rectangular_nest_normal.
Print Assumptions double_rectangular_nest_writes.
Print Assumptions double_rectangular_nest_exit_idempotent.
Print Assumptions double_rectangular_nest_exit_frame.
Print Assumptions double_rectangular_nest_settled_exit.
