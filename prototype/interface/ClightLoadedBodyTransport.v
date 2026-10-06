From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame ClightNoWrap
  ClightLoopSyntax ClightRegionProgress ClightLoopExecution ClightFrontendLoopProtocol.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightLoadedBodyPrefix ClightActiveLoopTransport
  ClightStrictIteration ClightStrictLoopProgress ClightQuietDeterminacy.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The domain proves body observation preservation, for example by a
    source-ordered scan. This language theorem then derives complete cached
    source execution. It does not assume that cached source execution as a
    prerequisite for checking the observation. *)
Section TRANSPORT.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variables row cache pointer : ident.
Variable body : statement.
Variables stable written : list ident.
Variables base : temp_env.
Variable initial : mem.
Variables block : block.
Variable offset : ptrofs.
Variable upper : int.
Hypotheses (CACHE : base!cache=Some(Vint upper)) (POINTER : base!pointer=Some(Vptr block offset)).
Hypotheses (CACHE_MEMBER : In cache stable) (POINTER_MEMBER : In pointer stable) (ROW_FRESH : ~In row stable).
Hypotheses (NORMAL : normal_statement body=true) (QUIET : quiet_statement body=true).
Hypothesis WRITES : writes_only written body.
Hypothesis ROW_UNWRITTEN : ~In row written.
Hypothesis STABLE_UNWRITTEN : forall identifier, In identifier stable -> ~In identifier written.
Let N := Int.signed upper.
Hypothesis NONNEGATIVE : 0<=N.
Hypothesis PRESERVE : forall i, 0<=i<N ->
  loaded_body_preserved fe row cache pointer body stable i (Entry ge locals base initial).

Definition loaded_body_snapshot limit temps memory := exists i,
  0<=i<=limit /\ temps!row=Some(Vint(Int.repr i)) /\ temp_agree stable base temps /\
  Mem.loadv Mint32 memory (Vptr block offset)=Some(Vint upper).

Theorem loaded_body_bound_cached temps memory trace after final outcome :
  loaded_body_snapshot N temps memory ->
  exec_stmt fe ge locals temps memory (loaded_bound_loop row pointer body) trace after final outcome ->
  exec_stmt fe ge locals temps memory (frontend_counted_loop row cache body) trace after final outcome /\
    loaded_body_snapshot N after final.
Proof.
  intros INV SOURCE.
  eapply strict_active_loop_transport with
    (invariant:=loaded_body_snapshot N) (body_invariant:=loaded_body_snapshot (N-1));
    [| | | |exact SOURCE|exact INV].
  - intros before mem flag [i [RANGE [ROW [FRAME READ]]]] TEST.
    eapply loaded_bound_cached_test; [rewrite FRAME by exact POINTER_MEMBER; exact POINTER|exact READ|
      rewrite FRAME by exact CACHE_MEMBER; exact CACHE|exact TEST].
  - intros before mem tr exit mem' out [i [RANGE [ROW [FRAME READ]]]] ACTIVE RUN.
    destruct (@loaded_bound_test_facts ge locals before mem row pointer true ACTIVE)
      as [word [bound [other [other_offset [WORD [BOUND [LOAD LT]]]]]]].
    assert (WORD_EQ : word=Int.repr i) by congruence; subst word.
    assert (ADDRESS : Vptr other other_offset=Vptr block offset)
      by (rewrite FRAME in BOUND by exact POINTER_MEMBER; congruence).
    injection ADDRESS as BLOCK OFFSET; subst other other_offset.
    assert (BOUND_EQ : bound=upper) by congruence; subst bound.
    assert (SMALL : 0<=i<N).
    { unfold Int.lt in LT; rewrite Int.signed_repr in LT by
        (pose proof (Int.signed_range upper); unfold N in RANGE; change Int.min_signed with (-2147483648) in *; lia).
      destruct (zlt i (Int.signed upper)); [unfold N; lia|discriminate]. }
    pose proof (@quiet_execution_silent fe ge locals before mem body tr exit mem' out RUN QUIET) as SILENT.
    pose proof (@normal_statement_execution fe ge locals body NORMAL before mem tr exit mem' out RUN) as EXIT.
    subst tr out.
    assert (READ' : Mem.loadv Mint32 mem' (Vptr block offset)=Some(Vint upper)).
    { rewrite (@PRESERVE i SMALL block offset before mem exit mem' POINTER ROW FRAME
        ltac:(cbn [entry_temps]; unfold temp_word; rewrite CACHE; exact READ) RUN); exact READ. }
    assert (ROW' : exit!row=Some(Vint(Int.repr i))).
    { rewrite (@writes_only_frame _ _ _ _ _ _ _ _ _ _ RUN written WRITES row ROW_UNWRITTEN); exact ROW. }
    assert (FRAME' : temp_agree stable before exit) by (eapply structured_temp_frame; eassumption).
    split; [exact RUN|exists i; split; [lia|split; [exact ROW'|split; [|exact READ']]]].
    eapply temp_agree_trans; eassumption.
  - intros before mem [i [RANGE REST]]; exists i; split; [lia|exact REST].
  - intros before mem tr exit mem' out [i [RANGE [ROW [FRAME READ]]]] RUN.
    assert (STRICT : strict_counter_active row before).
    { exists (Int.repr i); split; [exact ROW|rewrite Int.signed_repr;
        pose proof (Int.signed_range upper); unfold N in RANGE; change Int.min_signed with (-2147483648) in *; lia]. }
    destruct (@strict_increment_execution_exact fe ge locals row before mem tr exit mem' out STRICT RUN)
      as [_ [TEMPS [MEMORY _]]].
    subst exit mem'; rewrite (@counter_increment_small row before i ROW).
    exists (i+1); split; [lia|split; [apply PTree.gss|split; [|exact READ]]].
    intros identifier MEMBER; rewrite PTree.gso by (intro SAME; subst identifier; contradiction); apply FRAME; exact MEMBER.
Qed.

Theorem loaded_body_initial_cached after final :
  base!row=Some(Vint Int.zero) -> Mem.loadv Mint32 initial (Vptr block offset)=Some(Vint upper) ->
  exec_stmt fe ge locals base initial (loaded_bound_loop row pointer body) E0 after final Out_normal ->
  exec_stmt fe ge locals base initial (frontend_counted_loop row cache body) E0 after final Out_normal.
Proof.
  intros ROW READ SOURCE.
  assert (INV : loaded_body_snapshot N base initial).
  { exists 0; split; [lia|split; [exact ROW|split; [apply temp_agree_refl|exact READ]]]. }
  exact (proj1 (@loaded_body_bound_cached base initial E0 after final Out_normal INV SOURCE)).
Qed.
End TRANSPORT.

Print Assumptions loaded_body_bound_cached.
Print Assumptions loaded_body_initial_cached.
