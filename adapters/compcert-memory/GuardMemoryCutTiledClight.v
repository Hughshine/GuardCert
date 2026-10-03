From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import AbstractGuard SemanticFacts CompCertMemoryEquivalence
  ClightGuard ClightCondition ClightNoWrap ClightTempFrame ClightStraightLine
  ClightCountedLoop ClightLoopSyntax ClightRectangularStore ClightRectangularGuard
  ClightRectangularLoops ClightRectangularRegion ClightFrontendLoopProtocol
  ClightPrivateRule ClightProjectedExecution ClightTempFootprint.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles
  GuardMemoryLoops GuardMemoryPolyhedral GuardMemoryClightRectangles GuardMemoryPolyhedralRectangles
  GuardMemoryValidatedRectangles GuardMemoryTilingProgress GuardMemoryArrayBackend
  GuardMemoryTiledRectangles GuardMemoryTiledExecution GuardMemoryTiledClight
  GuardMemoryConditionalLoops GuardMemoryCutExecution GuardMemoryCutClight.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition checked_cut_tiling d bi bj a b c :=
  validate_memory_tiling_equivalence
    (memory_cut_source_program (rect_memory_write d 3%positive) (rectangle_stride d) a b c)
    (memory_cut_tiled_program (rect_memory_write d 3%positive) (rectangle_stride d) bi bj a b c)
    [rectangle_tiling_witness bi bj].
Definition compile_cut_tiled d array bound inner_bound live pool bi bj a b c :=
  compile_memory_array_loop d array 3%positive [bound;inner_bound]
    (rectangle_tiled_bounds d) live pool (memory_cut_tiled_loop (rect_memory_write d 3%positive) bi bj a b c).

Section SOURCE.
Variable d : rectangle_shape.
Hypothesis VALID : rectangle_layout_valid d.
Variable a b c : Z.
Hypothesis CLIMIT : 0 <= c.
Variable condition : expr.
Variable array row bound column inner_bound : ident.
Hypothesis CUT_COMPILE : compile_memory_cut_condition d row column a b c = Some condition.
Variable body outer_body : statement.
Hypothesis RN : row <> bound.
Hypothesis RC : row <> column.
Hypothesis NC : bound <> column.
Hypothesis RM : row <> inner_bound.
Hypothesis CM : column <> inner_bound.
Hypothesis BODY : flatten_region body = [memory_cut_statement d array row column condition].
Hypothesis OUTER : flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column inner_bound body].
Variable live : list ident.
Variable pool : list (ident * ident).
Variable bi bj : Z.
Hypothesis BI : 0 < bi.
Hypothesis BJ : 0 < bj.
Variable code : statement.
Hypothesis COMPILE : compile_cut_tiled d array bound inner_bound live pool bi bj a b c = Some code.
Hypothesis DEPENDENCES : mayReturn (checked_cut_tiling d bi bj a b c) true.

Theorem memory_cut_tiled_local fe ge locals le memory le' final N M :
  le ! row = Some (Vint Int.zero) -> le ! bound = Some (Vint (Int.repr N)) ->
  le ! inner_bound = Some (Vint (Int.repr M)) -> signed_range N -> signed_range M ->
  0 < N <= rectangle_outer_limit d -> 0 < M <= rectangle_stride d ->
  exec_stmt fe ge locals le memory (frontend_counted_loop row bound outer_body) E0 le' final Out_normal ->
  exists target_temps,
    exec_stmt fe ge locals le memory (rectangle_tiled_candidate code row bound column inner_bound)
      E0 target_temps final Out_normal /\ temp_agree live le' target_temps.
Proof.
  intros ZERO NLOOK MLOOK NS MS NB MB SOURCE.
  set (rows := Z.to_nat N); set (columns := Z.to_nat M).
  assert (RZ : Z.of_nat rows = N) by (unfold rows; apply Z2Nat.id; lia).
  assert (CZ : Z.of_nat columns = M) by (unfold columns; apply Z2Nat.id; lia).
  destruct (@memory_cut_source_clight_decode d VALID a b c condition array row bound column inner_bound
    CUT_COMPILE body outer_body RN RC NC RM CM BODY OUTER fe ge locals le memory le' final rows columns 3%positive
    CLIMIT ZERO ltac:(rewrite RZ; exact NLOOK) ltac:(rewrite CZ; exact MLOOK)
    ltac:(rewrite RZ; exact NS) ltac:(rewrite CZ; exact MS)
    ltac:(rewrite RZ; exact NB) ltac:(rewrite CZ; exact MB) SOURCE) as [block [ARRAY [LOOP EXIT]]].
  assert (NONALIAS : GuardMemoryInstr.NonAlias
    (RuntimeState (flat_array_locations 3%positive block (rectangle_extent d)) memory))
    by apply flat_array_locations_nonalias.
  pose proof (@validated_memory_cut_tiling (rect_memory_write d 3%positive) (rectangle_stride d)
    bi bj a b c rows columns _ _ BI BJ ltac:(rewrite CZ; lia) NONALIAS DEPENDENCES LOOP) as TILED.
  rewrite RZ,CZ in TILED,EXIT.
  destruct (@compile_memory_array_loop_within_correct d VALID fe ge locals array 3%positive block ARRAY
    [bound;inner_bound] (rectangle_tiled_bounds d) live pool
    (memory_cut_tiled_loop (rect_memory_write d 3%positive) bi bj a b c) code [N;M] le
    (RuntimeState (flat_array_locations 3%positive block (rectangle_extent d)) memory)
    (RuntimeState (flat_array_locations 3%positive block (rectangle_extent d)) final) memory COMPILE
    ltac:(apply rectangle_tiled_parameter_view; assumption)
    ltac:(apply rectangle_tiled_parameter_bounds; lia) TILED eq_refl)
    as [private_temps [private_memory [VIEW [FRAME EXEC]]]].
  unfold array_memory_view in VIEW; inversion VIEW; subst private_memory.
  assert (NEXIT : private_temps ! bound = Some (Vint (Int.repr N))).
  { rewrite FRAME by (cbn; auto); exact NLOOK. }
  assert (MEXIT : private_temps ! inner_bound = Some (Vint (Int.repr M))).
  { rewrite FRAME by (cbn; auto); exact MLOOK. }
  exists (PTree.set column (Vint (Int.repr M)) (PTree.set row (Vint (Int.repr N)) private_temps)); split.
  - unfold rectangle_tiled_candidate,rectangle_tiled_restore.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact EXEC|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); constructor; constructor;
      [exact NEXIT|rewrite PTree.gso by congruence; exact MEXIT].
  - rewrite rectangle_temps_commute by congruence; rewrite EXIT.
    apply temp_agree_restore; eapply temp_agree_weaken; [|exact FRAME].
    intros id MEMBER; apply in_or_app; right; exact MEMBER.
Qed.

Definition memory_cut_tiled_rule :
  encoded_private_rule live (frontend_counted_loop row bound outer_body)
    (rectangle_tiled_candidate code row bound column inner_bound).
Proof.
  assert (WRITES : writes_only [row;column] (frontend_counted_loop row bound outer_body)).
  { assert (BODY_WRITES : writes_only [] body) by (exact (@memory_cut_body_writes d array row column condition body BODY)).
    assert (OUTER_WRITES : writes_only [row;column] outer_body).
    { exact (@writes_only_weaken [column] [row;column] outer_body ltac:(cbn; tauto)
        (@rectangle_outer_writes column inner_bound body outer_body BODY_WRITES OUTER)). }
    unfold frontend_counted_loop,counter_increment.
    repeat constructor; cbn; auto. }
  refine {| private_rule_writes := [row;column]; private_rule_source_writes := WRITES;
    private_rule_atoms := unit; private_rule_domain := rectangle_guard_domain row bound inner_bound;
    private_rule_dimension := rectangle_guard_dimension row bound inner_bound VALID;
    private_rule_primitives := rectangle_guard_primitives row bound inner_bound VALID;
    private_rule_formula := Fact tt |}.
  - intros temps p locals le memory le' final RUN.
    exact (@memory_cut_source_guard_domain d condition (adapter_entry temps) (globalenv p) locals le memory
      array row bound column inner_bound body outer_body le' final RN RC NC CM BODY OUTER RUN).
  - intros temps p locals le memory le' final SCOPE RUN [ZERO [[ND NR] [MD MR]]].
    destruct ND as [n NLOOK]; destruct MD as [m MLOOK].
    cbn [entry_temps] in NLOOK,MLOOK,NR,MR; unfold temp_word in NR,MR;
      rewrite NLOOK in NR; rewrite MLOOK in MR.
    change (le ! row = Some (Vint Int.zero)) in ZERO.
    destruct (@memory_cut_tiled_local (adapter_entry temps) (globalenv p) locals le memory le' final
      (Int.signed n) (Int.signed m) ZERO ltac:(rewrite Int.repr_signed; exact NLOOK)
      ltac:(rewrite Int.repr_signed; exact MLOOK) (Int.signed_range n) (Int.signed_range m) NR MR RUN)
      as [target [EXEC FRAME]].
    exists target,final; split; [exact EXEC|split; [exact FRAME|apply memory_equivalent_refl]].
Defined.
End SOURCE.

Print Assumptions memory_cut_tiled_local.
Print Assumptions memory_cut_tiled_rule.
