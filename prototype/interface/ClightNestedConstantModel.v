From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightPureExpr ClightCountedLoop
  ClightLoopSyntax ClightLoopExecution ClightStraightLine ClightRectangularLoops
  ClightFrontendLoopProtocol ClightRegionProgress.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions.
From GuardAffineNest Require Import AffineNestSyntax.
From GuardInterface Require Import ClightConstantBoundModel ClightNestedExpressionTransport
  ClightStrictLoopProgress ClightActiveLoopTransport ClightExpressionHeaderCapture ClightQuietDeterminacy.
Import ListNotations.
Set Implicit Arguments.

Definition constant_affine_body_model iterator helper upper body :=
  Ssequence(Sset helper(memory_source_affine_code(MemorySourceConstant upper)))
    (Ssequence(rectangle_reset iterator)(frontend_counted_loop iterator helper body)).

Definition nested_constant_model_source row root_cache column child_cache child_helper iterator component_helper upper body :=
  frontend_counted_loop row root_cache
    (cached_child_model column child_cache child_helper(constant_affine_body_model iterator component_helper upper body)).

Definition nested_constant_model_nest row root_cache column child_cache child_helper iterator component_helper upper body child :=
  AffineSourceAxis row root_cache(MemorySourceTemp root_cache)
    (cached_child_model column child_cache child_helper(constant_affine_body_model iterator component_helper upper body))
    (AffineSourceAxis column child_helper(MemorySourceTemp child_cache)
      (constant_affine_body_model iterator component_helper upper body)
      (AffineSourceAxis iterator component_helper(MemorySourceConstant upper) body child)).

Lemma nested_constant_model_source_exact row root_cache column child_cache child_helper iterator component_helper upper body child :
  affine_nest_source(nested_constant_model_nest row root_cache column child_cache child_helper iterator component_helper upper body child)=
  nested_constant_model_source row root_cache column child_cache child_helper iterator component_helper upper body.
Proof. reflexivity. Qed.

Lemma nested_constant_model_shapes row root_cache column child_cache child_helper iterator component_helper upper body child :
  affine_nest_shapes(AffineSourceAxis iterator component_helper(MemorySourceConstant upper) body child) ->
  affine_nest_shapes(nested_constant_model_nest row root_cache column child_cache child_helper iterator component_helper upper body child).
Proof.
  intro SHAPES; unfold nested_constant_model_nest.
  split; [reflexivity|split; [reflexivity|exact SHAPES]].
Qed.

(** Use the affine library's actual constant syntax, including its negative
    branch, rather than assuming that every bound is a literal Econst_int. *)
Theorem constant_affine_body_preinitialized_model fe ge locals iterator helper upper body written
  temps memory after final :
  iterator<>helper -> writes_only written body -> ~In helper written ->
  temps!helper=Some(Vint(Int.repr upper)) ->
  exec_stmt fe ge locals temps memory(constant_body_source iterator(Int.repr upper) body) E0 after final Out_normal ->
  exec_stmt fe ge locals temps memory(constant_affine_body_model iterator helper upper body) E0 after final Out_normal /\
  after!helper=Some(Vint(Int.repr upper)).
Proof.
  intros DISTINCT WRITES PRIVATE WORD SOURCE.
  destruct(sequence_normal_decode SOURCE) as [reset [reset_memory [RESET LOOP]]].
  destruct(rectangle_reset_decode RESET) as [_ [TEMPS [MEMORY _]]]; subst reset reset_memory.
  assert (BOUND : (PTree.set iterator(Vint Int.zero)temps)!helper=Some(Vint(Int.repr upper))).
  { rewrite PTree.gso by congruence; exact WORD. }
  destruct(@constant_loop_preinitialized_model fe ge locals iterator helper(Int.repr upper) body written
    (PTree.set iterator(Vint Int.zero)temps) memory E0 after final Out_normal DISTINCT WRITES PRIVATE BOUND LOOP) as [MODEL EXIT].
  split; [|exact EXIT]; unfold constant_affine_body_model.
  eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=temps)(m1:=memory).
  - apply initialized_bound_assignment with(upper:=Int.repr upper); [exact WORD|].
    apply memory_source_affine_evaluation with(valuation:=fun _=>0%Z); intros identifier MEMBER; contradiction.
  - eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [exact RESET|exact MODEL].
Qed.

(** The source already has initialized private helpers. All inserted bound
    assignments write their existing values, so the internal execution has
    exactly the source's temps and memory. Original-entry preparation and its
    public projection are provided separately by the language library. *)
Section TRANSPORT.
Variables row column iterator root_cache child_cache child_helper component_helper : ident.
Variable child_upper : int.
Variable upper : Z.
Variable body : statement.
Variables leaf_written source_written protected : list ident.
Variable reference : temp_env.
Let original_body:=constant_body_source iterator(Int.repr upper) body.
Let model_body:=constant_affine_body_model iterator component_helper upper body.
Let original_row:=nested_cached_body column child_cache original_body.
Let model_row:=cached_child_model column child_cache child_helper model_body.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Hypothesis ITERATOR_HELPER : iterator<>component_helper.
Hypotheses (LEAF_WRITES : writes_only leaf_written body) (COMPONENT_PRIVATE : ~In component_helper leaf_written).
Hypotheses (NORMAL : normal_statement original_body=true) (QUIET : quiet_statement original_body=true).
Hypothesis SOURCE_WRITES : writes_only source_written original_body.
Hypothesis PROTECTED_UNWRITTEN : forall identifier,In identifier protected -> ~In identifier source_written.
Hypotheses (ROW_PRIVATE : ~In row protected) (COLUMN_PRIVATE : ~In column protected).
Hypotheses (CACHE_MEMBER : In child_cache protected) (CHILD_HELPER_MEMBER : In child_helper protected)
  (COMPONENT_HELPER_MEMBER : In component_helper protected).
Hypotheses (CACHE_WORD : reference!child_cache=Some(Vint child_upper))
  (CHILD_HELPER_WORD : reference!child_helper=Some(Vint child_upper))
  (COMPONENT_WORD : reference!component_helper=Some(Vint(Int.repr upper))).

Lemma nested_constant_original_row_normal : normal_statement original_row=true.
Proof.
  unfold original_row,nested_cached_body,frontend_counted_loop,strict_frontend_loop.
  cbn [normal_statement quiet_statement rectangle_reset]; rewrite QUIET; reflexivity.
Qed.

Lemma nested_constant_original_row_quiet : quiet_statement original_row=true.
Proof.
  unfold original_row,nested_cached_body,frontend_counted_loop,strict_frontend_loop.
  cbn [quiet_statement rectangle_reset]; rewrite QUIET; reflexivity.
Qed.

Lemma nested_constant_original_row_writes : writes_only(column::source_written) original_row.
Proof.
  unfold original_row,nested_cached_body,frontend_counted_loop,counter_increment,rectangle_reset.
  apply writes_sequence; [apply writes_set; cbn; auto|].
  apply writes_loop.
  - apply writes_sequence; [repeat constructor|].
    eapply writes_only_weaken; [|exact SOURCE_WRITES]; cbn; auto.
  - apply writes_sequence; [constructor|apply writes_set; cbn; auto].
Qed.

Lemma nested_constant_increment_frame cursor temps memory trace after final outcome :
  ~In cursor protected -> temp_agree protected reference temps ->
  exec_stmt fe ge locals temps memory(Ssequence Sskip(counter_increment cursor)) trace after final outcome ->
  temp_agree protected reference after.
Proof.
  intros PRIVATE FRAME RUN identifier MEMBER.
  rewrite(@writes_only_frame _ _ _ _ _ _ _ _ _ _ RUN [cursor]
    ltac:(unfold counter_increment; repeat constructor; cbn; auto) identifier
    ltac:(cbn; intuition congruence)); apply FRAME; exact MEMBER.
Qed.

(** The column body certificate is proved from the actual constant-source
    execution. It is not an optimizer-supplied semantic callback. *)
Theorem nested_constant_column_loop_model temps memory trace after final outcome :
  temp_agree protected reference temps ->
  exec_stmt fe ge locals temps memory(frontend_counted_loop column child_cache original_body) trace after final outcome ->
  exec_stmt fe ge locals temps memory(frontend_counted_loop column child_helper model_body) trace after final outcome /\
  temp_agree protected reference after.
Proof.
  intros FRAME SOURCE.
  eapply strict_active_loop_transport with(invariant:=fun le _=>temp_agree protected reference le)
    (body_invariant:=fun le _=>temp_agree protected reference le); [| | | |exact SOURCE|exact FRAME].
  - intros current before flag CURRENT TEST.
    destruct(@signed_expression_test_facts ge locals current before column(Etempvar child_cache type_int32s) flag
      eq_refl TEST) as [counter [word [COLUMN [EVAL RESULT]]]].
    apply scalar_temp_inv in EVAL.
    assert (WORD : word=child_upper).
    { rewrite CURRENT in EVAL by exact CACHE_MEMBER; congruence. }
    subst word flag; apply signed_expression_test_eval; [reflexivity|exact COLUMN|constructor].
    rewrite CURRENT by exact CHILD_HELPER_MEMBER; exact CHILD_HELPER_WORD.
  - intros current before tr exit last out CURRENT ACTIVE RUN.
    pose proof(@normal_statement_execution fe ge locals original_body NORMAL _ _ _ _ _ _ RUN) as OUTCOME.
    pose proof(@quiet_execution_silent fe ge locals _ _ original_body _ _ _ _ RUN QUIET) as SILENT; subst tr out.
    split.
    + exact(proj1(@constant_affine_body_preinitialized_model fe ge locals iterator component_helper upper body leaf_written
        current before exit last ITERATOR_HELPER LEAF_WRITES COMPONENT_PRIVATE
        ltac:(rewrite CURRENT by exact COMPONENT_HELPER_MEMBER; exact COMPONENT_WORD) RUN)).
    + intros identifier MEMBER.
      rewrite(@writes_only_frame _ _ _ _ _ _ _ _ _ _ RUN source_written SOURCE_WRITES identifier
        (PROTECTED_UNWRITTEN identifier MEMBER)); apply CURRENT; exact MEMBER.
  - intros; assumption.
  - intros; eapply nested_constant_increment_frame with(cursor:=column); eassumption.
Qed.

Theorem nested_constant_row_model temps memory after final :
  temp_agree protected reference temps ->
  exec_stmt fe ge locals temps memory original_row E0 after final Out_normal ->
  exec_stmt fe ge locals temps memory model_row E0 after final Out_normal /\ temp_agree protected reference after.
Proof.
  intros FRAME SOURCE.
  destruct(sequence_normal_decode SOURCE) as [reset [reset_memory [RESET LOOP]]].
  destruct(rectangle_reset_decode RESET) as [_ [TEMPS [MEMORY _]]]; subst reset reset_memory.
  assert (RESET_FRAME : temp_agree protected reference(PTree.set column(Vint Int.zero)temps)).
  { eapply temp_agree_trans; [exact FRAME|apply temp_agree_set; exact COLUMN_PRIVATE]. }
  destruct(@nested_constant_column_loop_model _ memory E0 after final Out_normal RESET_FRAME LOOP) as [MODEL EXIT].
  split; [|exact EXIT]; unfold model_row,cached_child_model,nested_cached_body.
  eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=temps)(m1:=memory).
  - apply initialized_bound_assignment with(upper:=child_upper).
    + rewrite FRAME by exact CHILD_HELPER_MEMBER; exact CHILD_HELPER_WORD.
    + constructor; rewrite FRAME by exact CACHE_MEMBER; exact CACHE_WORD.
  - eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [exact RESET|exact MODEL].
Qed.

Theorem nested_constant_preinitialized_model temps memory trace after final outcome :
  temp_agree protected reference temps ->
  exec_stmt fe ge locals temps memory(nested_cached_source row root_cache column child_cache original_body)
    trace after final outcome ->
  exec_stmt fe ge locals temps memory(nested_constant_model_source row root_cache column child_cache child_helper
    iterator component_helper upper body) trace after final outcome /\ temp_agree protected reference after.
Proof.
  intros FRAME SOURCE.
  eapply strict_active_loop_transport with(invariant:=fun le _=>temp_agree protected reference le)
    (body_invariant:=fun le _=>temp_agree protected reference le); [| | | |exact SOURCE|exact FRAME].
  - intros; assumption.
  - intros current before tr exit last out CURRENT ACTIVE RUN.
    pose proof(@normal_statement_execution fe ge locals original_row nested_constant_original_row_normal
      _ _ _ _ _ _ RUN) as OUTCOME.
    pose proof(@quiet_execution_silent fe ge locals _ _ original_row _ _ _ _ RUN nested_constant_original_row_quiet) as SILENT.
    subst tr out; eapply nested_constant_row_model; eassumption.
  - intros; assumption.
  - intros; eapply nested_constant_increment_frame with(cursor:=row); eassumption.
Qed.
End TRANSPORT.

(** Checked memory leaves write no temporaries. For the fixed three-axis
    shape, their quiet/write facts and name separation discharge all of the
    loop-transport premises above. Helper preparation remains a separate
    actual execution and source-scope transport. *)
Theorem nested_constant_closed_preinitialized_model fe ge locals row root_cache column child_cache child_helper
  iterator component_helper upper body child_upper temps memory trace after final outcome :
  NoDup [row;column;iterator;child_cache;child_helper;component_helper] ->
  quiet_statement body=true -> writes_only [] body ->
  temps!child_cache=Some(Vint child_upper) -> temps!child_helper=Some(Vint child_upper) ->
  temps!component_helper=Some(Vint(Int.repr upper)) ->
  exec_stmt fe ge locals temps memory
    (nested_cached_source row root_cache column child_cache(constant_body_source iterator(Int.repr upper) body))
    trace after final outcome ->
  exec_stmt fe ge locals temps memory
    (nested_constant_model_source row root_cache column child_cache child_helper iterator component_helper upper body)
    trace after final outcome.
Proof.
  intros DISTINCT QUIET WRITES CACHE CHILD COMPONENT SOURCE.
  assert (SOURCE_WRITES : writes_only [iterator](constant_body_source iterator(Int.repr upper) body)).
  { unfold constant_body_source,strict_frontend_loop,rectangle_reset,counter_increment.
    apply writes_sequence; [apply writes_set; cbn; auto|].
    apply writes_loop.
    - apply writes_sequence; [repeat constructor|].
      eapply writes_only_weaken; [|exact WRITES]; cbn; tauto.
    - apply writes_sequence; [constructor|apply writes_set; cbn; auto]. }
  assert (BODY_QUIET : quiet_statement(constant_body_source iterator(Int.repr upper) body)=true).
  { unfold constant_body_source,strict_frontend_loop,rectangle_reset,counter_increment.
    cbn [quiet_statement]; rewrite QUIET; reflexivity. }
  assert (BODY_NORMAL : normal_statement(constant_body_source iterator(Int.repr upper) body)=true).
  { unfold constant_body_source,strict_frontend_loop,rectangle_reset,counter_increment.
    cbn [normal_statement quiet_statement]; rewrite QUIET; reflexivity. }
  repeat match goal with H : NoDup(_::_) |- _ => inversion H; clear H; subst end.
  cbn in *.
  eapply (proj1(nested_constant_preinitialized_model child_helper
    (row:=row)(column:=column)(iterator:=iterator)(root_cache:=root_cache)
    (child_cache:=child_cache)(component_helper:=component_helper)
    (leaf_written:=[])(source_written:=[iterator])(protected:=[child_cache;child_helper;component_helper])
    (reference:=temps)(fe:=fe)(ge:=ge)(locals:=locals)
    ltac:(intuition congruence) WRITES ltac:(cbn; tauto) BODY_NORMAL BODY_QUIET SOURCE_WRITES
    ltac:(cbn; intuition congruence) ltac:(cbn; intuition congruence) ltac:(cbn; intuition congruence)
    ltac:(cbn; tauto) ltac:(cbn; tauto) ltac:(cbn; tauto) CACHE CHILD COMPONENT
    (temp_agree_refl _ _) SOURCE)).
Qed.

Print Assumptions nested_constant_model_source_exact.
Print Assumptions nested_constant_model_shapes.
Print Assumptions constant_affine_body_preinitialized_model.
Print Assumptions nested_constant_original_row_normal.
Print Assumptions nested_constant_original_row_quiet.
Print Assumptions nested_constant_original_row_writes.
Print Assumptions nested_constant_increment_frame.
Print Assumptions nested_constant_column_loop_model.
Print Assumptions nested_constant_row_model.
Print Assumptions nested_constant_preinitialized_model.
Print Assumptions nested_constant_closed_preinitialized_model.
