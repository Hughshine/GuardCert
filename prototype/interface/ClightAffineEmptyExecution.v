From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightNoWrap ClightCountedLoop
  ClightCountedProtocol ClightLoopExecution ClightFramedLoop ClightFrontendLoopProtocol ClightRectangularLoops.
From GuardMemory Require Import GuardMemoryVariableCounterExit.
From GuardInterface Require Import ClightAffineHeaderSnapshots ClightSignedExpressionProgress
  ClightStrictLoopProgress ClightExpressionHeaderCapture.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The public child counter is zero after a nonpositive child, while the
    public child bound retains its actual signed word. No leaf is evaluated. *)
Definition affine_empty_settle column inner_bound(upper:Z->Z)i temps :=
  PTree.set column(Vint Int.zero)(PTree.set inner_bound(Vint(Int.repr(upper i)))temps).

Lemma affine_empty_counter_exit row column inner_bound upper count x temps :
  row<>column -> row<>inner_bound -> column<>inner_bound ->
  memory_counter_exit row(affine_empty_settle column inner_bound upper)(S count)x temps=
  PTree.set row(Vint(Int.repr(x+Z.of_nat(S count))))
    (affine_empty_settle column inner_bound upper(x+Z.of_nat count)temps).
Proof.
  intros RC RK CK; revert x temps; induction count as [|count IH]; intros x temps.
  - cbn [memory_counter_exit]; rewrite Z.add_0_r; reflexivity.
  - change(memory_counter_exit row(affine_empty_settle column inner_bound upper)(S count)(x+1)
      (PTree.set row(Vint(Int.repr(x+1)))(affine_empty_settle column inner_bound upper x temps))=
      PTree.set row(Vint(Int.repr(x+Z.of_nat(S(S count)))))
        (affine_empty_settle column inner_bound upper(x+Z.of_nat(S count))temps)).
    rewrite IH; unfold affine_empty_settle.
    apply PTree.extensionality; intro id.
    destruct(peq id row)as [->|NR].
    + rewrite !PTree.gss; f_equal; f_equal; f_equal; rewrite !Nat2Z.inj_succ; lia.
    + rewrite !PTree.gso by congruence.
      destruct(peq id column)as [->|NC].
      * repeat first[rewrite PTree.gss|rewrite PTree.gso by congruence]; reflexivity.
      * rewrite !PTree.gso by congruence.
        destruct(peq id inner_bound)as [->|NK].
        -- repeat first[rewrite PTree.gss|rewrite PTree.gso by congruence];
             f_equal; f_equal; f_equal; f_equal; rewrite !Nat2Z.inj_succ; lia.
        -- rewrite !PTree.gso by congruence; reflexivity.
Qed.

Lemma strict_empty_false_execution fe ge locals temps memory row condition body :
  expression_test condition(Entry ge locals temps memory)false ->
  exec_stmt fe ge locals temps memory(strict_frontend_loop row condition body)E0 temps memory Out_normal.
Proof.
  intros [value[EVAL BOOL]]; eapply exec_Sloop_stop1 with(out':=Out_break).
  - eapply exec_Sseq_2 with(out:=Out_break); [|discriminate].
    eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [constructor|].
    eapply exec_Sifthenelse; [exact EVAL|exact BOOL|constructor].
  - constructor.
Qed.

Section EXECUTION.
Variable fe : genv->function->list val->mem->env->temp_env->mem->Prop.
Variable ge : genv.
Variable locals : env.
Variable memory : mem.
Variables row column inner_bound : ident.
Variables root_bound header : expr.
Variable body : statement.
Variable stable : list ident.
Variable base : temp_env.
Variable upper : Z->Z.
Variable N : Z.
Hypothesis DISTINCT : row<>column /\ row<>inner_bound /\ column<>inner_bound.
Hypothesis PRIVATE : ~In row stable /\ ~In column stable /\ ~In inner_bound stable.
Hypothesis ROOT_TYPE : typeof root_bound=type_int32s.
Hypothesis COUNT : 0<=N<=Int.max_signed.
Hypothesis ROOT : forall i temps,0<=i<=N -> temps!row=Some(Vint(Int.repr i)) ->
  temp_agree stable base temps -> eval_expr ge locals temps memory root_bound(Vint(Int.repr N)).
Hypothesis HEADER : forall i temps,0<=i<N -> temps!row=Some(Vint(Int.repr i)) ->
  temp_agree stable base temps -> eval_expr ge locals temps memory header(Vint(Int.repr(upper i))).
Hypothesis EMPTY : forall i,0<=i<N -> Int.lt Int.zero(Int.repr(upper i))=false.

Lemma affine_empty_body_execution i temps :
  0<=i<N -> temps!row=Some(Vint(Int.repr i)) -> temp_agree stable base temps ->
  exec_stmt fe ge locals temps memory(affine_setup_child column inner_bound header body)E0
    (affine_empty_settle column inner_bound upper i temps)memory Out_normal.
Proof.
  intros I ROW FRAME; destruct DISTINCT as [RC [RK CK]];
    unfold affine_setup_child,affine_empty_settle.
  eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)
    (le1:=PTree.set inner_bound(Vint(Int.repr(upper i)))temps)(m1:=memory).
  - apply exec_Sset; exact(@HEADER i temps I ROW FRAME).
  - eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)
      (le1:=PTree.set column(Vint Int.zero)(PTree.set inner_bound(Vint(Int.repr(upper i)))temps))(m1:=memory);
      [constructor; constructor|].
  apply frontend_zero_trip_encode.
  exists(Val.of_bool(Int.lt Int.zero(Int.repr(upper i)))); split.
  + eapply eval_Ebinop with(v1:=Vint Int.zero)(v2:=Vint(Int.repr(upper i))).
    * apply eval_Etempvar; apply PTree.gss.
    * apply eval_Etempvar; cbn [entry_temps].
      rewrite PTree.gso by congruence; apply PTree.gss.
    * reflexivity.
  + rewrite bool_of_bool,EMPTY by exact I; reflexivity.
Qed.

Theorem affine_empty_loop_execution count i temps :
  N=i+Z.of_nat count -> 0<=i -> temps!row=Some(Vint(Int.repr i)) ->
  temp_agree stable base temps ->
  exec_stmt fe ge locals temps memory(affine_setup_source row root_bound column inner_bound header body)E0
    (memory_counter_exit row(affine_empty_settle column inner_bound upper)count i temps)memory Out_normal.
Proof.
  destruct DISTINCT as [RC [RK CK]].
  revert i temps; induction count as [|count IH]; intros i temps LENGTH LOW ROW FRAME.
  - cbn in LENGTH; rewrite Z.add_0_r in LENGTH; subst N; cbn [memory_counter_exit].
    apply strict_empty_false_execution.
    pose proof(@signed_expression_test_eval ge locals temps memory row root_bound
      (Int.repr i)(Int.repr i)ROOT_TYPE ROW(@ROOT i temps ltac:(lia)ROW FRAME))as TEST.
    assert(SELF:Int.lt(Int.repr i)(Int.repr i)=false).
    { unfold Int.lt; destruct(zlt(Int.signed(Int.repr i))(Int.signed(Int.repr i))); [lia|reflexivity]. }
    rewrite SELF in TEST; exact TEST.
  - assert(I:0<=i<N)by(rewrite Nat2Z.inj_succ in LENGTH; lia).
    pose proof(@signed_expression_test_eval ge locals temps memory row root_bound
      (Int.repr i)(Int.repr N)ROOT_TYPE ROW(@ROOT i temps ltac:(lia)ROW FRAME))as TEST.
    assert(ACTIVE:Int.lt(Int.repr i)(Int.repr N)=true).
    { unfold Int.lt; rewrite !Int.signed_repr by(change Int.min_signed with(-2147483648); lia).
      destruct(zlt i N); [reflexivity|lia]. }
    rewrite ACTIVE in TEST; destruct TEST as [value[EVAL BOOL]].
    pose(settled:=affine_empty_settle column inner_bound upper i temps).
    assert(ROW_BODY:settled!row=Some(Vint(Int.repr i))).
    { unfold settled,affine_empty_settle; rewrite !PTree.gso by congruence; exact ROW. }
    assert(FRAME_BODY:temp_agree stable base settled).
    { eapply temp_agree_trans; [exact FRAME|].
      unfold settled,affine_empty_settle;
      eapply temp_agree_trans with(le1:=PTree.set inner_bound(Vint(Int.repr(upper i)))temps);
        [apply temp_agree_set; tauto|apply temp_agree_set; tauto]. }
    pose(next:=PTree.set row(Vint(Int.repr(i+1)))settled).
    assert(INCREMENT:exec_stmt fe ge locals settled memory(Ssequence Sskip(counter_increment row))
      E0 next memory Out_normal).
    { eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [constructor|].
      unfold next; apply counter_increment_at; [exact ROW_BODY|].
      unfold signed_range; change Int.min_signed with(-2147483648); lia. }
    assert(REST:exec_stmt fe ge locals next memory(affine_setup_source row root_bound column inner_bound header body)E0
      (memory_counter_exit row(affine_empty_settle column inner_bound upper)count(i+1)next)memory Out_normal).
    { apply IH.
      - rewrite Nat2Z.inj_succ in LENGTH; lia.
      - lia.
      - unfold next; apply PTree.gss.
      - eapply temp_agree_trans; [exact FRAME_BODY|unfold next; apply temp_agree_set; tauto]. }
    cbn [memory_counter_exit]; fold settled; fold next.
    unfold affine_setup_source in *.
    eapply exec_Sloop_loop with(t1:=E0)(t2:=E0)(t3:=E0)(out1:=Out_normal).
    + eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=temps)(m1:=memory);
        [|exact(@affine_empty_body_execution i temps I ROW FRAME)].
      eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [constructor|].
      eapply exec_Sifthenelse; [exact EVAL|exact BOOL|constructor].
    + constructor.
    + exact INCREMENT.
    + exact REST.
Qed.
End EXECUTION.

Print Assumptions affine_empty_counter_exit.
Print Assumptions strict_empty_false_execution.
Print Assumptions affine_empty_body_execution.
Print Assumptions affine_empty_loop_execution.
