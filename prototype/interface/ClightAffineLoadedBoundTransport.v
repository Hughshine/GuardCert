From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightCountedProtocol ClightFrontendLoopProtocol
  ClightTempFrame ClightRegionProgress ClightStraightLine ClightLoopSyntax ClightLoopExecution
  CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryParametricSourceClight.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightActiveLoopTransport
  ClightStrictIteration ClightQuietDeterminacy ClightStableLoopCondition ClightStrictLoopProgress.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma counted_observation_preserved point count start before after observation :
  (forall j, start <= j < start+Z.of_nat count -> forall first final,
    point j first final -> location_load observation final = location_load observation first) ->
  counted_iterations point count start before after ->
  location_load observation after = location_load observation before.
Proof.
  intros APART RUN; revert APART; induction RUN; intro APART.
  - reflexivity.
  - rewrite IHRUN.
    + apply APART with (j:=x); [rewrite Nat2Z.inj_succ; lia|exact H].
    + intros j RANGE; apply APART; rewrite Nat2Z.inj_succ; lia.
Qed.

Lemma loaded_bound_completed_header fe ge locals temps memory row parameter body trace after final outcome :
  exec_stmt fe ge locals temps memory (loaded_bound_loop row parameter body) trace after final outcome ->
  exists flag, expression_test (loaded_bound_test row parameter) (Entry ge locals temps memory) flag.
Proof.
  unfold loaded_bound_loop,strict_frontend_loop; intro SOURCE; inversion SOURCE; subst.
  all: match goal with HEADER : exec_stmt _ _ _ _ _
    (Ssequence (Ssequence Sskip (Sifthenelse _ _ _)) _) _ _ _ _ |- _ =>
      destruct (strict_header_execution HEADER) as [flag [TEST _]]; exists flag; exact TEST end.
Qed.

(** A reusable language bridge, with domain-specific decoding and point
    separations as explicit inputs. The initial load is a value observation;
    its preservation is derived from actual active rows, never put in D. *)
Section TRANSPORT.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variables row cache parameter column inner_bound : ident.
Variables outer_body : statement.
Variables point : Z -> Z -> mem -> mem -> Prop.
Variables upper : Z -> Z.
Variables stable : list ident.
Variable base : temp_env.
Variables block : block.
Variable offset : ptrofs.
Variable N : Z.
Hypothesis RANGE : 0 < N <= Int.max_signed.
Hypotheses (RC : row <> column) (RK : row <> inner_bound).
Hypotheses (SC : ~ In column stable) (SK : ~ In inner_bound stable) (SR : ~ In row stable).
Hypotheses (CACHE_MEMBER : In cache stable) (PARAMETER_MEMBER : In parameter stable).
Hypotheses (CACHE : base ! cache = Some (Vint (Int.repr N)))
  (POINTER : base ! parameter = Some (Vptr block offset)).
Hypotheses (QUIET : quiet_statement outer_body = true) (NORMAL : normal_statement outer_body = true).
Hypothesis UPPER : forall i, 0 <= i < N -> 0 <= upper i.
Hypothesis DECODE : forall i le memory after final,
  0 <= i < N -> le ! row = Some (Vint (Int.repr i)) -> temp_agree stable base le ->
  exec_stmt fe ge locals le memory outer_body E0 after final Out_normal ->
  counted_iterations (point i) (Z.to_nat (upper i)) 0 memory final /\
  after = memory_parametric_settle column inner_bound upper i le.
Hypothesis POINT : forall i j before after,
  0 <= i < N -> 0 <= j < upper i -> point i j before after ->
  location_load (MemoryLocation Mint32 block (Ptrofs.unsigned offset)) after =
  location_load (MemoryLocation Mint32 block (Ptrofs.unsigned offset)) before.

Definition affine_loaded_snapshot limit le memory := exists i,
  0 <= i <= limit /\ le ! row = Some (Vint (Int.repr i)) /\ temp_agree stable base le /\
  Mem.loadv Mint32 memory (Vptr block offset) = Some (Vint (Int.repr N)).

Theorem affine_loaded_bound_cached le memory trace after final outcome :
  affine_loaded_snapshot N le memory ->
  exec_stmt fe ge locals le memory (loaded_bound_loop row parameter outer_body) trace after final outcome ->
  exec_stmt fe ge locals le memory (frontend_counted_loop row cache outer_body) trace after final outcome /\
  affine_loaded_snapshot N after final.
Proof.
  intros INV SOURCE.
  eapply strict_active_loop_transport with
    (invariant:=affine_loaded_snapshot N) (body_invariant:=affine_loaded_snapshot (N-1));
    [| | | |exact SOURCE|exact INV].
  - intros before mem flag [i [IR [ROW [FRAME READ]]]] TEST.
    eapply loaded_bound_cached_test; [rewrite FRAME by exact PARAMETER_MEMBER; exact POINTER|exact READ|
      rewrite FRAME by exact CACHE_MEMBER; exact CACHE|exact TEST].
  - intros before mem tr exit mem' out [i [IR [ROW [FRAME READ]]]] ACTIVE RUN.
    destruct (@loaded_bound_test_facts ge locals before mem row parameter true ACTIVE)
      as [word [bound [other [other_offset [WORD [BOUND [LOAD LT]]]]]]].
    assert (WORD_EQ : word = Int.repr i) by congruence; subst word.
    assert (ADDRESS : Vptr other other_offset = Vptr block offset)
      by (rewrite FRAME in BOUND by exact PARAMETER_MEMBER; congruence).
    injection ADDRESS as BLOCK OFFSET; subst other other_offset.
    assert (BOUND_EQ : bound = Int.repr N) by congruence; subst bound.
    assert (SMALL : 0 <= i < N).
    { unfold Int.lt in LT; rewrite !Int.signed_repr in LT by
        (change Int.min_signed with (-2147483648); lia).
      destruct (zlt i N); [lia|discriminate]. }
    pose proof (@quiet_execution_silent fe ge locals before mem outer_body tr exit mem' out RUN QUIET) as SILENT.
    pose proof (@normal_statement_execution fe ge locals outer_body NORMAL before mem tr exit mem' out RUN) as EXIT.
    subst tr out.
    destruct (DECODE SMALL ROW FRAME RUN) as [ROWS TEMPS].
    assert (PRESERVED : Mem.loadv Mint32 mem' (Vptr block offset) = Mem.loadv Mint32 mem (Vptr block offset)).
    { cbn [Mem.loadv]; destruct (zle (Ptrofs.unsigned offset + size_chunk Mint32) Ptrofs.modulus);
        [|reflexivity].
      change (location_load (MemoryLocation Mint32 block (Ptrofs.unsigned offset)) mem' =
        location_load (MemoryLocation Mint32 block (Ptrofs.unsigned offset)) mem).
      eapply counted_observation_preserved; [|exact ROWS].
      intros j JR first last STEP; apply POINT with (i:=i) (j:=j); [exact SMALL| |exact STEP].
      rewrite Z2Nat.id in JR by (apply UPPER; exact SMALL); lia. }
    split; [exact RUN|exists i; split; [lia|split; [|split]]].
    + rewrite TEMPS; unfold memory_parametric_settle; repeat rewrite PTree.gso by congruence; exact ROW.
    + intros identifier MEMBER; rewrite TEMPS; unfold memory_parametric_settle;
        repeat rewrite PTree.gso by (intro BAD; subst identifier; contradiction); exact (FRAME identifier MEMBER).
    + rewrite PRESERVED; exact READ.
  - intros before mem [i [IR REST]]; exists i; split; [lia|exact REST].
  - intros before mem tr exit mem' out [i [IR [ROW [FRAME READ]]]] RUN.
    destruct (@strict_increment_execution_exact fe ge locals row before mem tr exit mem' out
      ltac:(exists (Int.repr i); split; [exact ROW|rewrite Int.signed_repr;
        change Int.min_signed with (-2147483648); lia]) RUN) as [_ [TEMPS [MEMORY _]]].
    subst exit mem'; rewrite (@counter_increment_small row before i ROW).
    exists (i+1); split; [lia|split; [apply PTree.gss|split; [|exact READ]]].
    intros identifier MEMBER; rewrite PTree.gso by (intro BAD; subst identifier; contradiction); exact (FRAME identifier MEMBER).
Qed.
End TRANSPORT.

Print Assumptions counted_observation_preserved.
Print Assumptions loaded_bound_completed_header.
Print Assumptions affine_loaded_bound_cached.
