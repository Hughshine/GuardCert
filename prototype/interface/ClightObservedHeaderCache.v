From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightNoWrap ClightTempFrame
  ClightLoopSyntax ClightLoopExecution ClightRegionProgress ClightFrontendLoopProtocol CompCertMemoryActions.
From GuardInterface Require Import ClightObservedHeaderPrefix ClightStrictLoopProgress ClightStrictIteration
  ClightActiveLoopTransport ClightAffineLoadedBoundTransport ClightQuietDeterminacy ClightReadonlyLoadedTreeSynthesis.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A successful domain check supplies preservation of all header observations.
    This language bridge then transports the actual compound-header source to
    the ordinary cached source consumed by existing optimizer certificates. *)
Section CACHE.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variables row cache : ident.
Variable header : expr.
Variable body : statement.
Variable stable : list ident.
Variable base : temp_env.
Variable observations : list (memory_location * val).
Variable N : Z.
Hypothesis RANGE : 0 <= N <= Int.max_signed.
Hypotheses (CACHE_MEMBER : In cache stable) (ROW_FRESH : ~ In row stable).
Hypothesis CACHE : base ! cache = Some (Vint (Int.repr N)).
Hypotheses (QUIET : quiet_statement body = true) (NORMAL : normal_statement body = true).
Variable upper : Z -> Z.
Variable point : Z -> Z -> mem -> mem -> Prop.
Hypothesis WIDTH : forall i, 0 <= i < N -> 0 <= upper i.
Hypothesis HEADER : forall i current memory,
  0 <= i <= N -> current ! row = Some (Vint (Int.repr i)) ->
  temp_agree stable base current -> header_observations_match observations memory ->
  expression_test header (Entry ge locals current memory) (i <? N).
Hypothesis DECODE : forall i current memory after final,
  0 <= i < N -> current ! row = Some (Vint (Int.repr i)) -> temp_agree stable base current ->
  exec_stmt fe ge locals current memory body E0 after final Out_normal ->
  counted_iterations (point i) (Z.to_nat (upper i)) 0 memory final /\
    after ! row = current ! row /\ temp_agree stable current after.
Hypothesis PRESERVE : forall observation, In observation observations -> forall i j before after,
  0 <= i < N -> 0 <= j < upper i -> point i j before after ->
  location_load (fst observation) after = location_load (fst observation) before.

Definition observed_header_cache_snapshot limit temps memory :=
  exists i, 0 <= i <= limit /\ temps ! row = Some (Vint (Int.repr i)) /\
    temp_agree stable base temps /\ header_observations_match observations memory.

Lemma observed_header_cached_test i current memory :
  0 <= i <= N -> current ! row = Some (Vint (Int.repr i)) -> temp_agree stable base current ->
  expression_test (counter_condition row cache) (Entry ge locals current memory) (i <? N).
Proof.
  intros I ROW FRAME; exists (Val.of_bool (i <? N)); split; [|apply bool_of_bool].
  eapply eval_Ebinop with (v1:=Vint (Int.repr i)) (v2:=Vint (Int.repr N)).
  - constructor; exact ROW.
  - constructor; rewrite FRAME by exact CACHE_MEMBER; exact CACHE.
  - change (Some (Val.of_bool (Int.lt (Int.repr i) (Int.repr N))) = Some (Val.of_bool (i <? N))).
    unfold Int.lt; rewrite !Int.signed_repr by (unfold signed_range; change Int.min_signed with (-2147483648); lia).
    destruct (zlt i N); [assert (FLAG : (i <? N)=true) by (apply Z.ltb_lt; lia)|
      assert (FLAG : (i <? N)=false) by (apply Z.ltb_ge; lia)]; rewrite FLAG; reflexivity.
Qed.

Theorem observed_header_cached_execution temps memory trace after final outcome :
  observed_header_cache_snapshot N temps memory ->
  exec_stmt fe ge locals temps memory (strict_frontend_loop row header body) trace after final outcome ->
  exec_stmt fe ge locals temps memory (frontend_counted_loop row cache body) trace after final outcome /\
    observed_header_cache_snapshot N after final.
Proof.
  intros INV SOURCE; eapply strict_active_loop_transport with
    (invariant:=observed_header_cache_snapshot N) (body_invariant:=observed_header_cache_snapshot (N-1));
    [| | | |exact SOURCE|exact INV].
  - intros current before flag [i [I [ROW [FRAME OBSERVED]]]] TEST.
    pose proof (@HEADER i current before I ROW FRAME OBSERVED) as EXPECTED.
    pose proof (readonly_test_determinate EXPECTED TEST) as SAME; subst flag.
    apply observed_header_cached_test; assumption.
  - intros current before tr exit last out [i [I [ROW [FRAME OBSERVED]]]] ACTIVE RUN.
    pose proof (@HEADER i current before I ROW FRAME OBSERVED) as EXPECTED.
    pose proof (readonly_test_determinate EXPECTED ACTIVE) as FLAG; apply Z.ltb_lt in FLAG.
    pose proof (@quiet_execution_silent fe ge locals current before body tr exit last out RUN QUIET) as SILENT.
    pose proof (@normal_statement_execution fe ge locals body NORMAL current before tr exit last out RUN) as OUTCOME.
    subst tr out; destruct (@DECODE i current before exit last ltac:(lia) ROW FRAME RUN) as [ITER [AFTER_ROW AFTER_FRAME]].
    split; [exact RUN|exists i; split; [lia|split; [rewrite AFTER_ROW; exact ROW|split; [|]]]].
    + eapply temp_agree_trans; [exact FRAME|exact AFTER_FRAME].
    + unfold header_observations_match in *; rewrite Forall_forall in OBSERVED |- *; intros observation MEMBER.
      assert (SAME : location_load (fst observation) last = location_load (fst observation) before).
      { eapply counted_observation_preserved; [|exact ITER].
        intros j J first finish STEP; apply PRESERVE with (i:=i) (j:=j); [exact MEMBER|lia| |exact STEP].
        rewrite Z2Nat.id in J by (apply WIDTH; lia); lia. }
      rewrite SAME; apply OBSERVED; exact MEMBER.
  - intros current before [i [I REST]]; exists i; split; [lia|exact REST].
  - intros current before tr exit last out [i [I [ROW [FRAME OBSERVED]]]] RUN.
    destruct (@strict_increment_execution_exact fe ge locals row current before tr exit last out
      ltac:(exists (Int.repr i); split; [exact ROW|rewrite Int.signed_repr;
        change Int.min_signed with (-2147483648); lia]) RUN) as [_ [TEMPS [MEMORY _]]].
    subst exit last; rewrite (@counter_increment_small row current i ROW).
    exists (i+1); split; [lia|split; [apply PTree.gss|split; [|exact OBSERVED]]].
    intros identifier MEMBER; rewrite PTree.gso by (intro SAME; subst identifier; contradiction); exact (FRAME identifier MEMBER).
Qed.
End CACHE.

Print Assumptions observed_header_cached_test.
Print Assumptions observed_header_cached_execution.
