From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightFramedLoop ClightTempFrame ClightNoWrap.
From GuardMemory Require Import GuardMemoryBooleanScan.
From GuardInterface Require Import ClightSharedGuard ClightPrivateScan.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition short_circuit_point flag body :=
  Ssequence body(Sifthenelse(shared_guard_choice flag) Sskip Sbreak).
Definition short_circuit_prefix_loop cursor bound flag body :=
  counted_loop cursor bound(short_circuit_point flag body).

Lemma short_circuit_point_execution fe ge locals current memory body after flag answer :
  exec_stmt fe ge locals current memory body E0 after memory Out_normal ->
  after!flag=Some(memory_boolean_word answer) ->
  exec_stmt fe ge locals current memory(short_circuit_point flag body) E0 after memory
    (if answer then Out_normal else Out_break).
Proof.
  intros BODY FLAG; unfold short_circuit_point.
  eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [exact BODY|].
  destruct(@shared_guard_choice_test ge locals after memory flag answer FLAG) as [value [EVAL BOOL]].
  eapply exec_Sifthenelse; [exact EVAL|exact BOOL|destruct answer; constructor].
Qed.

(** The invariant licenses only the next body. On refusal there is no
    recursive source-domain premise and no execution of a later body. *)
Section LOOP.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variables ge : genv.
Variable locals : env.
Variable memory : mem.
Variables cursor bound flag : ident.
Variable body : statement.
Variable live : list ident.
Variable base : temp_env.
Variables floor upper : Z.
Variable invariant : Z -> Prop.
Variable test : Z -> bool.
Hypotheses (DISTINCT : cursor<>bound) (CURSOR_FLAG : cursor<>flag) (BOUND_FLAG : bound<>flag)
  (CURSOR_PRIVATE : ~In cursor live) (UPPER : signed_range upper).
Hypothesis ADVANCE : forall index, floor<=index<upper -> invariant index -> test index=true -> invariant(index+1).
Hypothesis BODY : forall index current,
  signed_range index -> floor<=index<upper -> invariant index ->
  current!cursor=Some(Vint(Int.repr index)) -> current!bound=Some(Vint(Int.repr upper)) ->
  current!flag=Some(memory_boolean_word true) -> temp_agree live base current ->
  exists after,
    exec_stmt fe ge locals current memory body E0 after memory Out_normal /\
    temp_agree(cursor::bound::live) current after /\ after!flag=Some(memory_boolean_word(test index)).

Theorem short_circuit_prefix_loop_execution count : forall start current,
  upper=start+Z.of_nat count -> floor<=start -> signed_range start -> invariant start ->
  current!cursor=Some(Vint(Int.repr start)) -> current!bound=Some(Vint(Int.repr upper)) ->
  current!flag=Some(memory_boolean_word true) -> temp_agree live base current ->
  exists after,
    exec_stmt fe ge locals current memory(short_circuit_prefix_loop cursor bound flag body) E0 after memory Out_normal /\
    temp_agree live current after /\
    after!flag=Some(memory_boolean_word(memory_boolean_scan_result test start count)) /\
    (memory_boolean_scan_result test start count=true ->
      forall index, start<=index<upper -> invariant index /\ test index=true).
Proof.
  induction count as [|count IH]; intros start current LENGTH FLOOR START INV CURSOR BOUND FLAG FRAME.
  - assert(SAME:upper=start) by(cbn in LENGTH; lia); clear LENGTH; subst upper.
    exists current; split.
    + unfold short_circuit_prefix_loop,counted_loop; eapply exec_Sloop_stop1 with(out':=Out_break); [|constructor].
      destruct(@counter_condition_at ge locals current memory cursor bound start start DISTINCT CURSOR BOUND START UPPER)
        as [value [EVAL BOOL]]; rewrite Z.ltb_irrefl in BOOL.
      eapply exec_Sifthenelse; [exact EVAL|exact BOOL|constructor].
    + split; [apply temp_agree_refl|split; [exact FLAG|intros _ index RANGE; lia]].
  - assert(RANGE:floor<=start<upper) by(rewrite Nat2Z.inj_succ in LENGTH; lia).
    destruct(@BODY start current START RANGE INV CURSOR BOUND FLAG FRAME) as [middle [RUN [PUBLIC RESULT]]].
    destruct(@counter_condition_at ge locals current memory cursor bound start upper DISTINCT CURSOR BOUND START UPPER)
      as [value [EVAL BOOL]].
    assert(LT:(start<?upper)=true) by(apply Z.ltb_lt; lia); rewrite LT in BOOL.
    destruct(test start) eqn:CHECK.
    + assert(MID_CURSOR:middle!cursor=Some(Vint(Int.repr start))) by(rewrite PUBLIC by(left; reflexivity); exact CURSOR).
      assert(MID_BOUND:middle!bound=Some(Vint(Int.repr upper))) by(rewrite PUBLIC by(right; left; reflexivity); exact BOUND).
      assert(NEXT:signed_range(start+1)) by(unfold signed_range in *; lia).
      assert(NEXT_FRAME:temp_agree live current(counter_temps cursor middle(start+1))).
      { eapply temp_agree_trans; [eapply temp_agree_weaken; [|exact PUBLIC]|apply temp_agree_set; exact CURSOR_PRIVATE].
        intros identifier MEMBER; right; right; exact MEMBER. }
      destruct(IH(start+1)(counter_temps cursor middle(start+1))) as [after [REST [AFTER [EXIT CHECKED]]]].
      * rewrite Nat2Z.inj_succ in LENGTH; lia.
      * lia.
      * exact NEXT.
      * apply ADVANCE; assumption.
      * apply PTree.gss.
      * unfold counter_temps; rewrite PTree.gso by congruence; exact MID_BOUND.
      * unfold counter_temps; rewrite PTree.gso by congruence; exact RESULT.
      * eapply temp_agree_trans; [exact FRAME|exact NEXT_FRAME].
      * exists after; split.
        -- unfold short_circuit_prefix_loop,counted_loop.
           eapply exec_Sloop_loop with(out1:=Out_normal)(t1:=E0)(t2:=E0)(t3:=E0).
           ++ eapply exec_Sifthenelse; [exact EVAL|exact BOOL|].
              eapply short_circuit_point_execution with(answer:=true); [exact RUN|exact RESULT].
           ++ constructor.
           ++ exact(@counter_increment_at fe ge locals middle memory cursor start MID_CURSOR START).
           ++ exact REST.
        -- split; [eapply temp_agree_trans; [exact NEXT_FRAME|exact AFTER]|split].
           ++ cbn [memory_boolean_scan_result]; rewrite CHECK; exact EXIT.
           ++ cbn [memory_boolean_scan_result]; rewrite CHECK; cbn [andb].
              intros ACCEPT index INDEX; destruct(Z.eq_dec index start) as [->|OTHER].
              ** split; assumption.
              ** apply CHECKED; [exact ACCEPT|lia].
    + exists middle; split.
      * unfold short_circuit_prefix_loop,counted_loop; eapply exec_Sloop_stop1 with(out':=Out_break); [|constructor].
        eapply exec_Sifthenelse; [exact EVAL|exact BOOL|].
        eapply short_circuit_point_execution with(answer:=false); [exact RUN|exact RESULT].
      * split; [eapply temp_agree_weaken; [|exact PUBLIC]; intros identifier MEMBER; right; right; exact MEMBER|split].
        -- cbn [memory_boolean_scan_result]; rewrite CHECK; exact RESULT.
        -- cbn [memory_boolean_scan_result]; rewrite CHECK; discriminate.
Qed.
End LOOP.

Lemma short_circuit_prefix_loop_supported cursor bound flag body :
  private_scan_statement body -> private_scan_statement(short_circuit_prefix_loop cursor bound flag body).
Proof.
  intro BODY; unfold short_circuit_prefix_loop,short_circuit_point,counted_loop,counter_increment.
  auto 8 using scan_loop,scan_if,scan_sequence,scan_skip,scan_break,scan_set.
Qed.

Print Assumptions short_circuit_point_execution.
Print Assumptions short_circuit_prefix_loop_execution.
Print Assumptions short_circuit_prefix_loop_supported.
