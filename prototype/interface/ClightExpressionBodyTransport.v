From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightCountedLoop ClightTempFrame ClightNoWrap ClightRedundantSet
  ClightLoopSyntax ClightLoopExecution ClightRegionProgress ClightFrontendLoopProtocol CompCertMemoryActions.
From GuardInterface Require Import ClightObservedHeaderPrefix ClightExpressionHeaderCapture
  ClightSignedExpressionProgress ClightStrictLoopProgress ClightStrictIteration ClightActiveLoopTransport ClightQuietDeterminacy.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A language service for an arbitrary structured body, including an affine
    nest of any finite depth. Its domain client must prove that accepted
    checks preserve the observations of the actual expression header. *)
Section TRANSPORT.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variables row cache : ident.
Variable bound : expr.
Variable body : statement.
Variables stable written : list ident.
Variable base : temp_env.
Variable observations : list (memory_location * val).
Variable upper : int.
Hypothesis TYPE : typeof bound=type_int32s.
Hypothesis CACHE : base!cache=Some(Vint upper).
Hypotheses (CACHE_MEMBER : In cache stable) (ROW_FRESH : ~In row stable).
Hypotheses (NORMAL : normal_statement body=true) (QUIET : quiet_statement body=true).
Hypothesis WRITES : writes_only written body.
Hypothesis ROW_UNWRITTEN : ~In row written.
Hypothesis STABLE_UNWRITTEN : forall identifier, In identifier stable -> ~In identifier written.
Let N := Int.signed upper.
Hypothesis NONNEGATIVE : 0<=N.
Hypothesis HEADER : forall i current memory,
  0<=i<=N -> current!row=Some(Vint(Int.repr i)) -> temp_agree stable base current ->
  header_observations_match observations memory -> eval_expr ge locals current memory bound (Vint upper).
Hypothesis PRESERVE : forall i current memory after final,
  0<=i<N -> current!row=Some(Vint(Int.repr i)) -> temp_agree stable base current ->
  header_observations_match observations memory ->
  exec_stmt fe ge locals current memory body E0 after final Out_normal ->
  header_observations_match observations final.

Definition expression_body_snapshot limit temps memory := exists i,
  0<=i<=limit /\ temps!row=Some(Vint(Int.repr i)) /\ temp_agree stable base temps /\
  header_observations_match observations memory.

Lemma expression_body_header_flag i current memory flag :
  0<=i<=N -> current!row=Some(Vint(Int.repr i)) -> temp_agree stable base current ->
  header_observations_match observations memory ->
  expression_test (signed_expression_test row bound) (Entry ge locals current memory) flag ->
  flag=Int.lt (Int.repr i) upper.
Proof.
  intros RANGE ROW FRAME OBSERVED TEST.
  destruct (@signed_expression_test_facts _ _ _ _ _ _ _ TYPE TEST) as [word [value [COUNTER [EVAL FLAG]]]].
  pose proof (@HEADER i current memory RANGE ROW FRAME OBSERVED) as EXPECTED.
  pose proof (proj1(expressions_determinate ge locals current memory) _ _ EVAL _ EXPECTED) as SAME.
  assert (WORD : word=Int.repr i) by congruence.
  injection SAME as VALUE; subst word value; exact FLAG.
Qed.

Theorem expression_body_bound_cached temps memory trace after final outcome :
  expression_body_snapshot N temps memory ->
  exec_stmt fe ge locals temps memory
    (strict_frontend_loop row (signed_expression_test row bound) body) trace after final outcome ->
  exec_stmt fe ge locals temps memory (frontend_counted_loop row cache body) trace after final outcome /\
    expression_body_snapshot N after final.
Proof.
  intros INV SOURCE; eapply strict_active_loop_transport with
    (invariant:=expression_body_snapshot N) (body_invariant:=expression_body_snapshot (N-1));
    [| | | |exact SOURCE|exact INV].
  - intros current before flag [i [RANGE [ROW [FRAME OBSERVED]]]] TEST.
    pose proof (@expression_body_header_flag i current before flag RANGE ROW FRAME OBSERVED TEST) as FLAG; subst flag.
    apply signed_expression_test_eval; [reflexivity|exact ROW|apply eval_Etempvar].
    rewrite FRAME by exact CACHE_MEMBER; exact CACHE.
  - intros current before tr exit last out [i [RANGE [ROW [FRAME OBSERVED]]]] ACTIVE RUN.
    pose proof (@expression_body_header_flag i current before true RANGE ROW FRAME OBSERVED ACTIVE) as FLAG.
    assert (SMALL : 0<=i<N).
    { unfold Int.lt in FLAG; rewrite Int.signed_repr in FLAG by
        (pose proof (Int.signed_range upper); unfold N in RANGE; change Int.min_signed with (-2147483648) in *; lia).
      destruct (zlt i (Int.signed upper)); [unfold N; lia|discriminate]. }
    pose proof (@quiet_execution_silent fe ge locals current before body tr exit last out RUN QUIET) as SILENT.
    pose proof (@normal_statement_execution fe ge locals body NORMAL current before tr exit last out RUN) as EXIT.
    subst tr out.
    assert (ROW' : exit!row=Some(Vint(Int.repr i))).
    { rewrite (@writes_only_frame _ _ _ _ _ _ _ _ _ _ RUN written WRITES row ROW_UNWRITTEN); exact ROW. }
    assert (FRAME' : temp_agree stable current exit) by (eapply structured_temp_frame; eassumption).
    split; [exact RUN|exists i; split; [lia|split; [exact ROW'|split; [|]]]].
    + eapply temp_agree_trans; eassumption.
    + exact (@PRESERVE i current before exit last SMALL ROW FRAME OBSERVED RUN).
  - intros current before [i [RANGE REST]]; exists i; split; [lia|exact REST].
  - intros current before tr exit last out [i [RANGE [ROW [FRAME OBSERVED]]]] RUN.
    assert (STRICT : strict_counter_active row current).
    { exists (Int.repr i); split; [exact ROW|rewrite Int.signed_repr;
        pose proof (Int.signed_range upper); unfold N in RANGE; change Int.min_signed with (-2147483648) in *; lia]. }
    destruct (@strict_increment_execution_exact fe ge locals row current before tr exit last out STRICT RUN)
      as [_ [TEMPS [MEMORY _]]].
    subst exit last; rewrite (@counter_increment_small row current i ROW).
    exists (i+1); split; [lia|split; [apply PTree.gss|split; [|exact OBSERVED]]].
    intros identifier MEMBER; rewrite PTree.gso by (intro SAME; subst identifier; contradiction); apply FRAME; exact MEMBER.
Qed.

Theorem expression_body_initial_cached initial after final :
  base!row=Some(Vint Int.zero) -> header_observations_match observations initial ->
  exec_stmt fe ge locals base initial
    (strict_frontend_loop row (signed_expression_test row bound) body) E0 after final Out_normal ->
  exec_stmt fe ge locals base initial (frontend_counted_loop row cache body) E0 after final Out_normal.
Proof.
  intros ROW OBSERVED SOURCE.
  assert (INV : expression_body_snapshot N base initial).
  { exists 0; split; [lia|split; [exact ROW|split; [apply temp_agree_refl|exact OBSERVED]]]. }
  exact (proj1 (@expression_body_bound_cached base initial E0 after final Out_normal INV SOURCE)).
Qed.
End TRANSPORT.

Print Assumptions expression_body_header_flag.
Print Assumptions expression_body_bound_cached.
Print Assumptions expression_body_initial_cached.
