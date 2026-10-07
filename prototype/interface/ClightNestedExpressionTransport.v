From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame ClightNoWrap
  ClightLoopSyntax ClightLoopExecution ClightRegionProgress ClightFrontendLoopProtocol
  ClightStraightLine ClightRectangularLoops CompCertMemoryActions.
From GuardInterface Require Import ClightObservedHeaderPrefix ClightExpressionHeaderCapture
  ClightExpressionBodyTransport ClightNestedExpressionCapture ClightSignedExpressionProgress
  ClightStrictLoopProgress ClightStrictIteration ClightActiveLoopTransport ClightQuietDeterminacy.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition nested_cached_body column child_cache body :=
  Ssequence (rectangle_reset column) (frontend_counted_loop column child_cache body).
Definition nested_cached_source row cache column child_cache body :=
  frontend_counted_loop row cache (nested_cached_body column child_cache body).

(** A single row consumes only the preservation checks for that row. The
    outer prefix can use this before the checks for later rows exist. *)
Theorem nested_expression_row_cached fe ge locals row column child_cache child_bound body stable written
  base observations child_upper i current memory after final :
  typeof child_bound=type_int32s -> base!child_cache=Some(Vint child_upper) -> In child_cache stable ->
  ~In row stable -> ~In column stable -> row<>column ->
  normal_statement body=true -> quiet_statement body=true -> writes_only written body ->
  ~In row written -> ~In column written -> (forall id,In id stable -> ~In id written) ->
  0<=Int.signed child_upper ->
  (forall j temps mem, 0<=j<=Int.signed child_upper ->
    temps!row=Some(Vint(Int.repr i)) -> temps!column=Some(Vint(Int.repr j)) ->
    temp_agree stable base temps -> header_observations_match observations mem ->
    eval_expr ge locals temps mem child_bound (Vint child_upper)) ->
  (forall j temps mem exit last, 0<=j<Int.signed child_upper ->
    temps!row=Some(Vint(Int.repr i)) -> temps!column=Some(Vint(Int.repr j)) ->
    temp_agree stable base temps -> header_observations_match observations mem ->
    exec_stmt fe ge locals temps mem body E0 exit last Out_normal ->
    header_observations_match observations last) ->
  current!row=Some(Vint(Int.repr i)) -> temp_agree stable base current ->
  header_observations_match observations memory ->
  exec_stmt fe ge locals current memory (nested_expression_body column child_bound body) E0 after final Out_normal ->
  exec_stmt fe ge locals current memory (nested_cached_body column child_cache body) E0 after final Out_normal /\
  header_observations_match observations final.
Proof.
  intros TYPE CACHE CACHE_MEMBER ROW_FRESH COLUMN_FRESH DISTINCT NORMAL QUIET WRITES ROW_UNWRITTEN
    COLUMN_UNWRITTEN STABLE_UNWRITTEN NONNEGATIVE HEADER PRESERVE ROW FRAME OBSERVED SOURCE.
  destruct (sequence_normal_decode SOURCE) as [reset [reset_memory [RESET CHILD]]].
  destruct (rectangle_reset_decode RESET) as [_ [TEMPS [MEMORY _]]]; subst reset reset_memory.
  pose (inner_base := PTree.set row (Vint(Int.repr i)) base).
  assert (INNER_FRAME : temp_agree (row::stable) inner_base (PTree.set column (Vint Int.zero) current)).
  { intros id [SAME|MEMBER].
    - subst id; unfold inner_base; rewrite PTree.gso by exact DISTINCT; rewrite PTree.gss; exact ROW.
    - unfold inner_base; rewrite !PTree.gso by (intro SAME; subst id; contradiction); apply FRAME; exact MEMBER. }
  assert (INV : expression_body_snapshot column (row::stable) inner_base observations (Int.signed child_upper)
    (PTree.set column (Vint Int.zero) current) memory).
  { exists 0; split; [lia|split; [apply PTree.gss|split; assumption]]. }
  destruct (@expression_body_bound_cached fe ge locals column child_cache child_bound body (row::stable) written
    inner_base observations child_upper TYPE
    ltac:(unfold inner_base; rewrite PTree.gso by (intro SAME; subst row; contradiction); exact CACHE)
    ltac:(right; exact CACHE_MEMBER) ltac:(cbn; tauto) NORMAL QUIET WRITES COLUMN_UNWRITTEN
    ltac:(intros id [SAME|MEMBER]; [subst id; exact ROW_UNWRITTEN|apply STABLE_UNWRITTEN; exact MEMBER])
    ltac:(intros j temps mem JR COLUMN_WORD INNER OBS; eapply HEADER; [exact JR| |exact COLUMN_WORD| |exact OBS];
      [rewrite (INNER row (or_introl eq_refl)); unfold inner_base; apply PTree.gss|
       intros id MEMBER; rewrite (INNER id (or_intror MEMBER)); unfold inner_base;
         rewrite PTree.gso by (intro SAME; subst id; contradiction); reflexivity])
    ltac:(intros j temps mem exit last JR COLUMN_WORD INNER OBS RUN;
      eapply PRESERVE; [exact JR| |exact COLUMN_WORD| |exact OBS|exact RUN];
      [rewrite (INNER row (or_introl eq_refl)); unfold inner_base; apply PTree.gss|
       intros id MEMBER; rewrite (INNER id (or_intror MEMBER)); unfold inner_base;
         rewrite PTree.gso by (intro SAME; subst id; contradiction); reflexivity])
    _ memory E0 after final Out_normal INV CHILD) as [CACHED [j [RANGE [COLUMN [EXIT FINAL]]]]].
  split; [unfold nested_cached_body; eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); eassumption|exact FINAL].
Qed.

(** All previously captured observations are carried through the inner loop.
    Preserving just the child header would not license the next outer header. *)
Section TRANSPORT.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variables row cache column child_cache : ident.
Variables bound child_bound : expr.
Variable body : statement.
Variables stable written : list ident.
Variable base : temp_env.
Variable observations : list (memory_location * val).
Variables upper child_upper : int.
Hypotheses (TYPE : typeof bound=type_int32s) (CHILD_TYPE : typeof child_bound=type_int32s).
Hypotheses (CACHE : base!cache=Some(Vint upper)) (CHILD_CACHE : base!child_cache=Some(Vint child_upper)).
Hypotheses (CACHE_MEMBER : In cache stable) (CHILD_CACHE_MEMBER : In child_cache stable).
Hypotheses (ROW_FRESH : ~In row stable) (COLUMN_FRESH : ~In column stable) (DISTINCT : row<>column).
Hypotheses (NORMAL : normal_statement body=true) (QUIET : quiet_statement body=true).
Hypothesis WRITES : writes_only written body.
Hypotheses (ROW_UNWRITTEN : ~In row written) (COLUMN_UNWRITTEN : ~In column written).
Hypothesis STABLE_UNWRITTEN : forall id, In id stable -> ~In id written.
Hypothesis CHILD_NONNEGATIVE : 0<=Int.signed child_upper.
Hypothesis HEADER : forall i current memory,
  0<=i<=Int.signed upper -> current!row=Some(Vint(Int.repr i)) ->
  temp_agree stable base current -> header_observations_match observations memory ->
  eval_expr ge locals current memory bound (Vint upper).
Hypothesis CHILD_HEADER : forall i j current memory,
  0<=i<Int.signed upper -> 0<=j<=Int.signed child_upper ->
  current!row=Some(Vint(Int.repr i)) -> current!column=Some(Vint(Int.repr j)) ->
  temp_agree stable base current -> header_observations_match observations memory ->
  eval_expr ge locals current memory child_bound (Vint child_upper).
Hypothesis PRESERVE : forall i j current memory after final,
  0<=i<Int.signed upper -> 0<=j<Int.signed child_upper ->
  current!row=Some(Vint(Int.repr i)) -> current!column=Some(Vint(Int.repr j)) ->
  temp_agree stable base current -> header_observations_match observations memory ->
  exec_stmt fe ge locals current memory body E0 after final Out_normal ->
  header_observations_match observations final.

Lemma nested_expression_child_cached i current memory after final :
  0<=i<Int.signed upper -> current!row=Some(Vint(Int.repr i)) ->
  current!column=Some(Vint Int.zero) -> temp_agree stable base current ->
  header_observations_match observations memory ->
  exec_stmt fe ge locals current memory
    (strict_frontend_loop column (signed_expression_test column child_bound) body)
    E0 after final Out_normal ->
  exec_stmt fe ge locals current memory (frontend_counted_loop column child_cache body)
    E0 after final Out_normal /\ header_observations_match observations final.
Proof.
  intros RANGE ROW COLUMN FRAME OBSERVED SOURCE.
  pose (inner_base := PTree.set row (Vint(Int.repr i)) base).
  assert (INNER_FRAME : temp_agree (row::stable) inner_base current).
  { intros id [SAME|MEMBER]; [subst id; unfold inner_base; rewrite PTree.gss; exact ROW|].
    unfold inner_base; rewrite PTree.gso by (intro SAME; subst id; contradiction); apply FRAME; exact MEMBER. }
  assert (INV : expression_body_snapshot column (row::stable) inner_base observations
      (Int.signed child_upper) current memory).
  { exists 0; split; [lia|split; [exact COLUMN|split; [exact INNER_FRAME|exact OBSERVED]]]. }
  destruct (@expression_body_bound_cached fe ge locals column child_cache child_bound body
    (row::stable) written inner_base observations child_upper CHILD_TYPE
    ltac:(unfold inner_base; rewrite PTree.gso by (intro SAME; subst row; contradiction); exact CHILD_CACHE)
    ltac:(right; exact CHILD_CACHE_MEMBER) ltac:(cbn; tauto) NORMAL QUIET WRITES COLUMN_UNWRITTEN
    ltac:(intros id [SAME|MEMBER]; [subst id; exact ROW_UNWRITTEN|apply STABLE_UNWRITTEN; exact MEMBER])
    ltac:(intros j temps mem JR COLUMN_WORD INNER OBS;
      eapply CHILD_HEADER; [exact RANGE|exact JR| |exact COLUMN_WORD| |exact OBS];
      [rewrite (INNER row (or_introl eq_refl)); unfold inner_base; rewrite PTree.gss; reflexivity|
       intros id MEMBER; rewrite (INNER id (or_intror MEMBER)); unfold inner_base;
         rewrite PTree.gso by (intro SAME; subst id; contradiction); reflexivity])
    ltac:(intros j temps mem exit last JR COLUMN_WORD INNER OBS RUN;
      eapply PRESERVE; [exact RANGE|exact JR| |exact COLUMN_WORD| |exact OBS|exact RUN];
      [rewrite (INNER row (or_introl eq_refl)); unfold inner_base; rewrite PTree.gss; reflexivity|
       intros id MEMBER; rewrite (INNER id (or_intror MEMBER)); unfold inner_base;
         rewrite PTree.gso by (intro SAME; subst id; contradiction); reflexivity])
    current memory E0 after final Out_normal INV SOURCE) as [CACHED EXIT].
  split; [exact CACHED|destruct EXIT as [j [JR [COLUMN_WORD [FRAME_EXIT OBS_EXIT]]]]; exact OBS_EXIT].
Qed.

Lemma nested_expression_body_cached i current memory after final :
  0<=i<Int.signed upper -> current!row=Some(Vint(Int.repr i)) ->
  temp_agree stable base current -> header_observations_match observations memory ->
  exec_stmt fe ge locals current memory (nested_expression_body column child_bound body)
    E0 after final Out_normal ->
  exec_stmt fe ge locals current memory (nested_cached_body column child_cache body)
    E0 after final Out_normal /\ header_observations_match observations final.
Proof.
  intros RANGE ROW FRAME OBSERVED SOURCE.
  destruct (sequence_normal_decode SOURCE) as [reset [reset_memory [RESET CHILD]]].
  destruct (rectangle_reset_decode RESET) as [_ [TEMPS [MEMORY _]]]; subst reset reset_memory.
  destruct (@nested_expression_child_cached i (PTree.set column (Vint Int.zero) current) memory after final
    RANGE ltac:(rewrite PTree.gso by congruence; exact ROW) (PTree.gss _ _ _)
    ltac:(intros id MEMBER; rewrite PTree.gso by (intro SAME; subst id; contradiction); apply FRAME; exact MEMBER)
    OBSERVED CHILD) as [CACHED FINAL].
  split; [unfold nested_cached_body; eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); eassumption|exact FINAL].
Qed.

Theorem nested_expression_bound_cached temps memory trace after final outcome :
  expression_body_snapshot row stable base observations (Int.signed upper) temps memory ->
  exec_stmt fe ge locals temps memory (nested_expression_source row bound column child_bound body)
    trace after final outcome ->
  exec_stmt fe ge locals temps memory (nested_cached_source row cache column child_cache body)
    trace after final outcome /\
  expression_body_snapshot row stable base observations (Int.signed upper) after final.
Proof.
  intros INV SOURCE; eapply strict_active_loop_transport with
    (invariant:=expression_body_snapshot row stable base observations (Int.signed upper))
    (body_invariant:=expression_body_snapshot row stable base observations (Int.signed upper-1));
    [| | | |exact SOURCE|exact INV].
  - intros current before flag [i [RANGE [ROW [FRAME OBSERVED]]]] TEST.
    destruct (@signed_expression_test_facts _ _ _ _ _ _ _ TYPE TEST)
      as [word [value [COUNTER [EVAL FLAG]]]].
    pose proof (@HEADER i current before RANGE ROW FRAME OBSERVED) as EXPECTED.
    pose proof (proj1(expressions_determinate ge locals current before) _ _ EVAL _ EXPECTED) as SAME.
    injection SAME as VALUE; assert (WORD : word=Int.repr i) by congruence; subst word value flag.
    apply signed_expression_test_eval; [reflexivity|exact ROW|apply eval_Etempvar].
    rewrite FRAME by exact CACHE_MEMBER; exact CACHE.
  - intros current before tr exit last out [i [RANGE [ROW [FRAME OBSERVED]]]] ACTIVE RUN.
    destruct (@signed_expression_test_facts _ _ _ _ _ _ _ TYPE ACTIVE)
      as [word [value [COUNTER [EVAL FLAG]]]].
    pose proof (@HEADER i current before RANGE ROW FRAME OBSERVED) as EXPECTED.
    pose proof (proj1(expressions_determinate ge locals current before) _ _ EVAL _ EXPECTED) as SAME.
    injection SAME as VALUE; assert (WORD : word=Int.repr i) by congruence; subst word value.
    assert (SMALL : 0<=i<Int.signed upper).
    { unfold Int.lt in FLAG; rewrite Int.signed_repr in FLAG by
        (pose proof (Int.signed_range upper); change Int.min_signed with (-2147483648) in *; lia).
      destruct (zlt i (Int.signed upper)); [lia|discriminate]. }
    pose proof (@quiet_execution_silent fe ge locals current before _ tr exit last out RUN
      (@nested_expression_body_quiet column child_bound body QUIET)) as SILENT.
    pose proof (@normal_statement_execution fe ge locals _
      (@nested_expression_body_normal column child_bound body QUIET) current before tr exit last out RUN) as NORMAL_EXIT.
    subst tr out.
    destruct (@nested_expression_body_cached i current before exit last SMALL ROW FRAME OBSERVED RUN) as [CACHED FINAL].
    assert (BODY_WRITES : writes_only (column::written) (nested_expression_body column child_bound body)).
    { unfold nested_expression_body,rectangle_reset,strict_frontend_loop,counter_increment.
      constructor; [constructor; left; reflexivity|constructor; [constructor; [repeat constructor|]|constructor; [constructor|constructor; left; reflexivity]]].
      eapply writes_only_weaken; [|exact WRITES]; intros id MEMBER; right; exact MEMBER. }
    assert (ROW' : exit!row=Some(Vint(Int.repr i))).
    { rewrite (@writes_only_frame _ _ _ _ _ _ _ _ _ _ RUN (column::written) BODY_WRITES row ltac:(cbn; intros [SAME|BAD]; [apply DISTINCT; symmetry; exact SAME|apply ROW_UNWRITTEN; exact BAD])); exact ROW. }
    assert (FRAME' : temp_agree stable current exit).
    { eapply structured_temp_frame; [exact BODY_WRITES| |exact RUN].
      intros id MEMBER; cbn; intros [SAME|BAD]; [subst id; contradiction|apply (STABLE_UNWRITTEN id MEMBER); exact BAD]. }
    split; [exact CACHED|exists i; split; [lia|split; [exact ROW'|split; [eapply temp_agree_trans; eassumption|exact FINAL]]]].
  - intros current before [i [RANGE REST]]; exists i; split; [lia|exact REST].
  - intros current before tr exit last out [i [RANGE [ROW [FRAME OBSERVED]]]] RUN.
    assert (STRICT : strict_counter_active row current).
    { exists (Int.repr i); split; [exact ROW|rewrite Int.signed_repr;
        pose proof (Int.signed_range upper); change Int.min_signed with (-2147483648) in *; lia]. }
    destruct (@strict_increment_execution_exact fe ge locals row current before tr exit last out STRICT RUN)
      as [_ [TEMPS [MEMORY _]]].
    subst exit last; rewrite (@counter_increment_small row current i ROW).
    exists (i+1); split; [lia|split; [apply PTree.gss|split; [|exact OBSERVED]]].
    intros id MEMBER; rewrite PTree.gso by (intro SAME; subst id; contradiction); apply FRAME; exact MEMBER.
Qed.

Theorem nested_expression_initial_cached memory after final :
  0<=Int.signed upper -> base!row=Some(Vint Int.zero) ->
  header_observations_match observations memory ->
  exec_stmt fe ge locals base memory (nested_expression_source row bound column child_bound body)
    E0 after final Out_normal ->
  exec_stmt fe ge locals base memory (nested_cached_source row cache column child_cache body)
    E0 after final Out_normal /\ header_observations_match observations final.
Proof.
  intros NONNEGATIVE ROW OBSERVED SOURCE.
  assert (INV : expression_body_snapshot row stable base observations (Int.signed upper) base memory).
  { exists 0; split; [lia|split; [exact ROW|split; [apply temp_agree_refl|exact OBSERVED]]]. }
  destruct (@nested_expression_bound_cached base memory E0 after final Out_normal INV SOURCE) as [CACHED EXIT].
  split; [exact CACHED|destruct EXIT as [i [RANGE [LAST_ROW [FRAME FINAL]]]]; exact FINAL].
Qed.
End TRANSPORT.

Print Assumptions nested_expression_child_cached.
Print Assumptions nested_expression_row_cached.
Print Assumptions nested_expression_body_cached.
Print Assumptions nested_expression_bound_cached.
Print Assumptions nested_expression_initial_cached.
