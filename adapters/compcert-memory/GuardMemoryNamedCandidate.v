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
  GuardMemoryTiledRectangles GuardMemoryTiledExecution GuardMemoryTiledClight GuardMemoryArrayFamilyBackend
  GuardMemorySequenceLoops GuardMemorySequencePolyhedral GuardMemorySequenceExecution GuardMemorySequenceClight GuardMemoryOperationsClight GuardMemoryFlatArrayBackend GuardMemoryExtractorProgress GuardMemoryReindexedExtractor GuardMemoryEquivalentDomainsExtractor GuardMemoryProposedClight GuardMemoryMultipleArrays GuardMemoryRegistryBackend
  GuardMemoryRegistryGuard GuardMemoryNamedOperations GuardMemoryNamedRegistrySource GuardMemoryNamedClight GuardMemoryNamedGuard.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_named_candidate_certificate base operations candidate :=
  forall N M initial final,
    0 < N <= rectangle_outer_limit base -> 0 < M <= rectangle_stride base ->
    GuardMemoryInstr.NonAlias initial ->
    L.loop_semantics (memory_rectangle_sequence (map named_operation_instruction operations)) [N;M] initial final ->
    L.loop_semantics candidate [N;M] initial final.
Definition compile_named_array_candidate base operations bound inner_bound live pool candidate :=
  compile_memory_registry_loop (named_array_descriptors base operations) [bound;inner_bound]
    (rectangle_tiled_bounds base) live pool candidate.

Section SOURCE.
Variable d : rectangle_shape.
Hypothesis VALID : rectangle_layout_valid d.
Variable operations : list named_array_operation.
Hypothesis LAYOUTS : Forall (named_operation_layout d) operations.
Variable row bound column inner_bound : ident.
Variable body outer_body : statement.
Hypothesis RN : row <> bound.
Hypothesis RC : row <> column.
Hypothesis NC : bound <> column.
Hypothesis RM : row <> inner_bound.
Hypothesis CM : column <> inner_bound.
Hypothesis BODY : flatten_region body = map (named_operation_statement row column) operations.
Hypothesis OUTER : flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column inner_bound body].
Variable live : list ident.
Variable pool : list (ident * ident).
Variable candidate : L.stmt.
Variable code : statement.
Hypothesis COMPILE : compile_named_array_candidate d operations bound inner_bound live pool candidate = Some code.
Hypothesis CANDIDATE : memory_named_candidate_certificate d operations candidate.

Theorem memory_named_array_candidate_local fe ge locals le memory le' final N M :
  le ! row = Some (Vint Int.zero) -> le ! bound = Some (Vint (Int.repr N)) ->
  le ! inner_bound = Some (Vint (Int.repr M)) -> signed_range N -> signed_range M ->
  0 < N <= rectangle_outer_limit d -> 0 < M <= rectangle_stride d ->
  memory_registry_guard_property (named_array_descriptors d operations) (Entry ge locals le memory) ->
  exec_stmt fe ge locals le memory (frontend_counted_loop row bound outer_body) E0 le' final Out_normal ->
  exists target_temps,
    exec_stmt fe ge locals le memory (rectangle_tiled_candidate code row bound column inner_bound)
      E0 target_temps final Out_normal /\ temp_agree live le' target_temps.
Proof.
  intros ZERO NLOOK MLOOK NS MS NB MB ALIAS SOURCE.
  set (rows := Z.to_nat N); set (columns := Z.to_nat M).
  assert (RZ : Z.of_nat rows = N) by (unfold rows; apply Z2Nat.id; lia).
  assert (CZ : Z.of_nat columns = M) by (unfold columns; apply Z2Nat.id; lia).
  destruct (@named_array_operations_source_clight_decode d VALID operations LAYOUTS
    row bound column inner_bound body outer_body RN RC NC RM CM BODY OUTER
    fe ge locals le memory le' final rows columns ZERO
    ltac:(rewrite RZ; exact NLOOK) ltac:(rewrite CZ; exact MLOOK)
    ltac:(rewrite RZ; exact NS) ltac:(rewrite CZ; exact MS)
    ltac:(rewrite RZ; exact NB) ltac:(rewrite CZ; exact MB) SOURCE)
    as [entries [ARRAYS [IDS [POINTERS [LOOP EXIT]]]]].
  destruct ALIAS as [other_entries [OTHER_ARRAYS BLOCKS]].
  assert (SAME_BLOCKS : map memory_array_block entries = map memory_array_block other_entries).
  { rewrite <- (@memory_descriptor_blocks_binding (named_array_descriptors d operations) entries
      (Entry ge locals le memory) ARRAYS).
    rewrite <- (@memory_descriptor_blocks_binding (named_array_descriptors d operations) other_entries
      (Entry ge locals le memory) OTHER_ARRAYS); reflexivity. }
  assert (NONALIAS : GuardMemoryInstr.NonAlias (RuntimeState (memory_array_registry entries) memory)).
  { apply memory_array_registry_nonalias; rewrite SAME_BLOCKS; exact BLOCKS. }
  rewrite RZ,CZ in LOOP,EXIT.
  pose proof (@CANDIDATE N M (RuntimeState (memory_array_registry entries) memory)
    (RuntimeState (memory_array_registry entries) final) NB MB NONALIAS LOOP) as TARGET.
  destruct (@compile_memory_registry_loop_correct (named_array_descriptors d operations) entries
    fe ge locals ARRAYS [bound;inner_bound] (rectangle_tiled_bounds d) live pool
    candidate code [N;M] le (RuntimeState (memory_array_registry entries) memory)
    (RuntimeState (memory_array_registry entries) final) memory COMPILE
    ltac:(apply rectangle_tiled_parameter_view; assumption)
    ltac:(apply rectangle_tiled_parameter_bounds; lia) TARGET eq_refl)
    as [private_temps [private_memory [VIEW [FRAME EXEC]]]].
  unfold memory_registry_view in VIEW; inversion VIEW; subst private_memory.
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

Lemma memory_named_source_domain fe ge locals le memory le' final :
  exec_stmt fe ge locals le memory (frontend_counted_loop row bound outer_body) E0 le' final Out_normal ->
  memory_named_guard_domain d (named_array_descriptors d operations) row bound inner_bound (Entry ge locals le memory).
Proof.
  intro SOURCE.
  assert (DOMAIN : rectangle_guard_domain row bound inner_bound (Entry ge locals le memory)).
  { exact (@named_array_operations_source_guard_domain operations fe ge locals le memory row bound column inner_bound
      body outer_body le' final RN RC NC CM BODY OUTER SOURCE). }
  split; [exact DOMAIN|]; intro ACCEPT.
  destruct (@rectangle_guard_accept_sound d row bound inner_bound VALID tt (Entry ge locals le memory) DOMAIN ACCEPT)
    as [ZERO [[ND NR] [MD MR]]].
  destruct ND as [n NLOOK]; destruct MD as [m MLOOK].
  cbn [entry_temps] in NLOOK,MLOOK,NR,MR; unfold temp_word in NR,MR; rewrite NLOOK in NR; rewrite MLOOK in MR.
  change (le ! row = Some (Vint Int.zero)) in ZERO.
  set (rows := Z.to_nat (Int.signed n)); set (columns := Z.to_nat (Int.signed m)).
  assert (RZ : Z.of_nat rows = Int.signed n) by (unfold rows; apply Z2Nat.id; lia).
  assert (CZ : Z.of_nat columns = Int.signed m) by (unfold columns; apply Z2Nat.id; lia).
  destruct (@named_array_operations_source_clight_decode d VALID operations LAYOUTS
    row bound column inner_bound body outer_body RN RC NC RM CM BODY OUTER
    fe ge locals le memory le' final rows columns ZERO
    ltac:(rewrite RZ,Int.repr_signed; exact NLOOK) ltac:(rewrite CZ,Int.repr_signed; exact MLOOK)
    ltac:(rewrite RZ; apply Int.signed_range) ltac:(rewrite CZ; apply Int.signed_range)
    ltac:(rewrite RZ; exact NR) ltac:(rewrite CZ; exact MR) SOURCE)
    as [entries [ARRAYS [IDS [POINTERS [LOOP EXIT]]]]].
  exists entries; split; assumption.
Qed.

Definition memory_named_array_candidate_rule :
  encoded_private_rule live (frontend_counted_loop row bound outer_body)
    (rectangle_tiled_candidate code row bound column inner_bound).
Proof.
  assert (WRITES : writes_only [row;column] (frontend_counted_loop row bound outer_body)).
  { assert (BODY_WRITES : writes_only [] body) by (exact (@named_array_operations_body_writes operations row column body BODY)).
    assert (OUTER_WRITES : writes_only [row;column] outer_body).
    { exact (@writes_only_weaken [column] [row;column] outer_body ltac:(cbn; tauto)
        (@rectangle_outer_writes column inner_bound body outer_body BODY_WRITES OUTER)). }
    unfold frontend_counted_loop,counter_increment.
    repeat constructor; cbn; auto. }
  refine {| private_rule_writes := [row;column]; private_rule_source_writes := WRITES;
    private_rule_atoms := unit; private_rule_domain := memory_named_guard_domain d (named_array_descriptors d operations) row bound inner_bound;
    private_rule_dimension := memory_named_guard_dimension (named_array_descriptors d operations) row bound inner_bound VALID;
    private_rule_primitives := memory_named_guard_primitives (named_array_descriptors d operations) row bound inner_bound VALID;
    private_rule_formula := Fact tt |}.
  - intros temps p locals le memory le' final RUN.
    exact (@memory_named_source_domain (adapter_entry temps) (globalenv p) locals le memory le' final RUN).
  - intros temps p locals le memory le' final SCOPE RUN [[ZERO [[ND NR] [MD MR]]] ALIAS].
    destruct ND as [n NLOOK]; destruct MD as [m MLOOK].
    cbn [entry_temps] in NLOOK,MLOOK,NR,MR; unfold temp_word in NR,MR;
      rewrite NLOOK in NR; rewrite MLOOK in MR.
    change (le ! row = Some (Vint Int.zero)) in ZERO.
    destruct (@memory_named_array_candidate_local (adapter_entry temps) (globalenv p) locals le memory le' final
      (Int.signed n) (Int.signed m) ZERO ltac:(rewrite Int.repr_signed; exact NLOOK)
      ltac:(rewrite Int.repr_signed; exact MLOOK) (Int.signed_range n) (Int.signed_range m) NR MR ALIAS RUN)
      as [target [EXEC FRAME]].
    exists target,final; split; [exact EXEC|split; [exact FRAME|apply memory_equivalent_refl]].
Defined.
End SOURCE.
Print Assumptions memory_named_array_candidate_local.
Print Assumptions memory_named_source_domain.
Print Assumptions memory_named_array_candidate_rule.
