From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame
  ClightRectangularLoops ClightLoopExecution ClightFrontendLoopProtocol
  ClightRegionProgress ClightLoopSyntax.
From GuardInterface Require Import ClightAffineHeaderSnapshots ClightStrictIteration
  ClightStrictLoopProgress ClightQuietDeterminacy ClightExpressionHeaderCapture.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition empty_child_temps column inner_bound word temps :=
  PTree.set column (Vint Int.zero) (PTree.set inner_bound (Vint word) temps).

(** An inactive child has no body execution requirement. In particular this
    theorem does not require its loads, addresses or scalar inputs to exist. *)
Theorem affine_setup_empty_child_run fe ge locals temps memory column inner_bound header body word :
  column<>inner_bound -> eval_expr ge locals temps memory header(Vint word) ->
  Int.lt Int.zero word=false ->
  exec_stmt fe ge locals temps memory(affine_setup_child column inner_bound header body)
    E0(empty_child_temps column inner_bound word temps)memory Out_normal.
Proof.
  intros DISTINCT VALUE INACTIVE; unfold affine_setup_child,empty_child_temps.
  eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [constructor; exact VALUE|].
  eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [constructor; constructor|].
  apply frontend_zero_trip_encode.
  rewrite <-INACTIVE; apply signed_expression_test_eval.
  - reflexivity.
  - apply PTree.gss.
  - apply eval_Etempvar; rewrite PTree.gso by congruence; apply PTree.gss.
Qed.

Theorem affine_setup_empty_child_exact fe ge locals temps memory column inner_bound header body word after final :
  column<>inner_bound -> quiet_statement body=true ->
  eval_expr ge locals temps memory header(Vint word) -> Int.lt Int.zero word=false ->
  exec_stmt fe ge locals temps memory(affine_setup_child column inner_bound header body)
    E0 after final Out_normal ->
  after=empty_child_temps column inner_bound word temps /\ final=memory.
Proof.
  intros DISTINCT QUIET VALUE INACTIVE SOURCE.
  destruct(@quiet_execution_determinate fe ge locals temps memory
    (affine_setup_child column inner_bound header body)E0 after final Out_normal SOURCE
    (@affine_setup_child_quiet column inner_bound header body QUIET)E0
    (empty_child_temps column inner_bound word temps)memory Out_normal
    (@affine_setup_empty_child_run fe ge locals temps memory column inner_bound header body word
      DISTINCT VALUE INACTIVE))as [_ [TEMPS [MEMORY _]]]; auto.
Qed.

(** This is proof-time source-prefix recovery, not emitted execution of the
    source before the guard. Domain clients provide safe header computations;
    the language proof establishes that the empty prefix changes no memory. *)
Section PREFIX.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variables ge : genv.
Variable locals : env.
Variable original : temp_env.
Variable memory : mem.
Variables row column inner_bound : ident.
Variables root_header child_header : expr.
Variable body : statement.
Variable stable : list ident.
Variable count : Z.
Hypotheses (CK:column<>inner_bound)(RC:row<>column)(RK:row<>inner_bound).
Hypotheses (NORMAL:normal_statement body=true)(QUIET:quiet_statement body=true).
Hypothesis PROTECTED : forall identifier,In identifier stable ->
  identifier<>row /\ identifier<>column /\ identifier<>inner_bound.
Hypothesis COUNT : count<=Int.max_signed.
Hypothesis ACTIVE : forall i current,0<=i<count -> current!row=Some(Vint(Int.repr i)) ->
  temp_agree stable original current ->
  expression_test root_header(Entry ge locals current memory)true.

Theorem leading_empty_rows_recover skip after final :
  0<=Z.of_nat skip<=count -> original!row=Some(Vint Int.zero) ->
  (forall i current,0<=i<Z.of_nat skip -> current!row=Some(Vint(Int.repr i)) ->
    temp_agree stable original current -> exists word,
      eval_expr ge locals current memory child_header(Vint word) /\ Int.lt Int.zero word=false) ->
  exec_stmt fe ge locals original memory
    (strict_frontend_loop row root_header(affine_setup_child column inner_bound child_header body))
    E0 after final Out_normal ->
  exists reached,reached!row=Some(Vint(Int.repr(Z.of_nat skip))) /\
    temp_agree stable original reached /\
    exec_stmt fe ge locals reached memory
      (strict_frontend_loop row root_header(affine_setup_child column inner_bound child_header body))
      E0 after final Out_normal.
Proof.
  induction skip as [|skip IH]; intros RANGE ZERO EMPTY SOURCE.
  - exists original; cbn; split; [exact ZERO|split; [apply temp_agree_refl|exact SOURCE]].
  - destruct(IH ltac:(rewrite Nat2Z.inj_succ in RANGE; lia)ZERO
      ltac:(intros i current I ROW FRAME; apply(EMPTY i current); [rewrite Nat2Z.inj_succ; lia|exact ROW|exact FRAME])SOURCE)
      as [current [ROW [FRAME TAIL]]].
    assert(INDEX:0<=Z.of_nat skip<count)by(rewrite Nat2Z.inj_succ in RANGE; lia).
    destruct(@strict_active_iteration fe ge locals row root_header
      (affine_setup_child column inner_bound child_header body)current memory after final
      (@affine_setup_child_normal column inner_bound child_header body QUIET)
      (@affine_setup_child_quiet column inner_bound child_header body QUIET)
      (ACTIVE INDEX ROW FRAME)TAIL)
      as [body_after [body_final [next [next_memory [BODY [INC REST]]]]]].
    destruct(EMPTY(Z.of_nat skip)current ltac:(rewrite Nat2Z.inj_succ; lia)ROW FRAME)
      as [word [VALUE INACTIVE]].
    destruct(@affine_setup_empty_child_exact fe ge locals current memory column inner_bound
      child_header body word body_after body_final CK QUIET VALUE INACTIVE BODY)as [BODY_TEMPS BODY_MEMORY].
    subst body_after body_final.
    assert(BODY_ROW:(empty_child_temps column inner_bound word current)!row=Some(Vint(Int.repr(Z.of_nat skip)))).
    { unfold empty_child_temps; rewrite !PTree.gso by congruence; exact ROW. }
    assert(STRICT:strict_counter_active row(empty_child_temps column inner_bound word current)).
    { exists(Int.repr(Z.of_nat skip)); split; [exact BODY_ROW|].
      rewrite Int.signed_repr by(unfold signed_range; change Int.min_signed with(-2147483648); lia).
      lia. }
    destruct(@strict_increment_execution_exact fe ge locals row
      (empty_child_temps column inner_bound word current)memory E0 next next_memory Out_normal STRICT INC)
      as [_ [NEXT [MEMORY _]]].
    subst next next_memory.
    rewrite(@counter_increment_small row(empty_child_temps column inner_bound word current)
      (Z.of_nat skip)BODY_ROW)in REST.
    exists(PTree.set row(Vint(Int.repr(Z.of_nat skip+1)))
      (empty_child_temps column inner_bound word current)); split.
    + rewrite Nat2Z.inj_succ; apply PTree.gss.
    + split; [|exact REST].
      intros identifier MEMBER; destruct(PROTECTED identifier MEMBER)as [R [C K]].
      unfold empty_child_temps; rewrite !PTree.gso by congruence; exact(FRAME identifier MEMBER).
Qed.

Theorem leading_empty_rows_body_receipt skip after final :
  0<=Z.of_nat skip<count -> original!row=Some(Vint Int.zero) ->
  (forall i current,0<=i<Z.of_nat skip -> current!row=Some(Vint(Int.repr i)) ->
    temp_agree stable original current -> exists word,
      eval_expr ge locals current memory child_header(Vint word) /\ Int.lt Int.zero word=false) ->
  exec_stmt fe ge locals original memory
    (strict_frontend_loop row root_header(affine_setup_child column inner_bound child_header body))
    E0 after final Out_normal ->
  exists reached next last,reached!row=Some(Vint(Int.repr(Z.of_nat skip))) /\
    temp_agree stable original reached /\
    exec_stmt fe ge locals reached memory(affine_setup_child column inner_bound child_header body)
      E0 next last Out_normal.
Proof.
  intros RANGE ZERO EMPTY SOURCE.
  destruct(@leading_empty_rows_recover skip after final ltac:(lia)ZERO EMPTY SOURCE)as [reached [ROW [FRAME TAIL]]].
  destruct(@strict_active_iteration fe ge locals row root_header
    (affine_setup_child column inner_bound child_header body)reached memory after final
    (@affine_setup_child_normal column inner_bound child_header body QUIET)
    (@affine_setup_child_quiet column inner_bound child_header body QUIET)
    (ACTIVE RANGE ROW FRAME)TAIL)as [next [last [later [later_memory [BODY REST]]]]].
  exists reached,next,last; auto.
Qed.
End PREFIX.

(** A reached active setup supplies its actual leaf execution. The header may
    contain loads. Its value is licensed separately and need not be pure. *)
Theorem affine_setup_active_child_receipt fe ge locals temps memory column inner_bound header body word
    after final stable :
  column<>inner_bound -> normal_statement body=true -> quiet_statement body=true ->
  (forall identifier,In identifier stable -> identifier<>column /\ identifier<>inner_bound) ->
  eval_expr ge locals temps memory header(Vint word) -> Int.lt Int.zero word=true ->
  exec_stmt fe ge locals temps memory(affine_setup_child column inner_bound header body)
    E0 after final Out_normal ->
  exists leaf next last,temp_agree stable temps leaf /\
    exec_stmt fe ge locals leaf memory body E0 next last Out_normal.
Proof.
  intros CK NORMAL QUIET PROTECTED VALUE POSITIVE SOURCE.
  unfold affine_setup_child in SOURCE.
  destruct(sequence_normal_decode SOURCE)as [assigned [assigned_memory [SET TAIL]]].
  inversion SET; subst assigned assigned_memory.
  match goal with EVAL:eval_expr _ _ _ _ header ?other |- _ =>
    pose proof(proj1(expressions_determinate ge locals temps memory)_ _ VALUE _ EVAL)as SAME;
    subst other end.
  destruct(sequence_normal_decode TAIL)as [reset [reset_memory [RESET CHILD]]].
  destruct(rectangle_reset_decode RESET)as [_ [TEMPS [MEMORY _]]]; subst reset reset_memory.
  assert(TEST:expression_test(counter_condition column inner_bound)
    (Entry ge locals(empty_child_temps column inner_bound word temps)memory)true).
  { rewrite <-POSITIVE; apply signed_expression_test_eval; [reflexivity|apply PTree.gss|].
    apply eval_Etempvar; unfold empty_child_temps; rewrite PTree.gso by congruence; apply PTree.gss. }
  change(frontend_counted_loop column inner_bound body)with
    (strict_frontend_loop column(counter_condition column inner_bound)body)in CHILD.
  destruct(@strict_active_iteration fe ge locals column(counter_condition column inner_bound)body
    (empty_child_temps column inner_bound word temps)memory after final NORMAL QUIET TEST CHILD)
    as [next [last [later [later_memory [LEAF REST]]]]].
  exists(empty_child_temps column inner_bound word temps),next,last; split; [|exact LEAF].
  intros identifier MEMBER; destruct(PROTECTED identifier MEMBER)as [C K].
  unfold empty_child_temps; rewrite !PTree.gso by congruence; reflexivity.
Qed.

Print Assumptions affine_setup_empty_child_run.
Print Assumptions affine_setup_empty_child_exact.
Print Assumptions leading_empty_rows_recover.
Print Assumptions leading_empty_rows_body_receipt.
Print Assumptions affine_setup_active_child_receipt.
