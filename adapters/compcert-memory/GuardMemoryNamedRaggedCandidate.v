From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import AbstractGuard SemanticFacts CompCertMemoryEquivalence
  ClightGuard ClightCondition ClightNoWrap ClightTempFrame ClightStraightLine ClightCountedLoop
  ClightRectangularStore ClightRectangularGuard ClightRectangularLoops ClightLoopSyntax ClightFrontendLoopProtocol
  ClightPrivateRule ClightProjectedExecution ClightTempFootprint.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryArrayBackend
  GuardMemoryTiledClight GuardMemoryMultipleArrays GuardMemoryRegistryBackend GuardMemoryRegistryGuard GuardMemoryNamedOperations
  GuardMemoryNamedRegistrySource GuardMemoryNamedCandidate GuardMemoryRaggedLoops GuardMemoryRaggedClight
  GuardMemoryRaggedGuard GuardMemoryNamedRaggedSource GuardMemoryRaggedBackend.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_ragged_candidate_certificate base operations candidate :=
  forall N M initial final,
    0 < N <= rectangle_outer_limit base -> 0 < M <= rectangle_stride base ->
    N+M-1 <= rectangle_stride base -> GuardMemoryInstr.NonAlias initial ->
    L.loop_semantics (memory_ragged_sequence (map named_operation_instruction operations)) [N;M] initial final ->
    L.loop_semantics candidate [N;M] initial final.
Definition memory_ragged_exit_bound bound parameter := Ebinop Oadd
  (Ebinop Oadd (Etempvar bound type_int32s) (Econst_int (Int.repr (-1)) type_int32s) type_int32s)
  (Etempvar parameter type_int32s) type_int32s.
Definition memory_ragged_restore row bound column inner_bound parameter :=
  Ssequence (Sset inner_bound (memory_ragged_exit_bound bound parameter))
    (Ssequence (Sset column (Etempvar inner_bound type_int32s)) (Sset row (Etempvar bound type_int32s))).
Definition memory_ragged_candidate code row bound column inner_bound parameter :=
  Ssequence code (memory_ragged_restore row bound column inner_bound parameter).
Lemma memory_ragged_restore_execution fe ge locals le memory row bound column inner_bound parameter N M :
  bound <> inner_bound -> bound <> column ->
  le ! bound = Some (Vint (Int.repr N)) -> le ! parameter = Some (Vint (Int.repr M)) ->
  exec_stmt fe ge locals le memory (memory_ragged_restore row bound column inner_bound parameter) E0
    (PTree.set row (Vint (Int.repr N)) (memory_ragged_settle column inner_bound M (N-1) le)) memory Out_normal.
Proof.
  intros NK NC NLOOK MLOOK.
  unfold memory_ragged_restore,memory_ragged_settle.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0)
    (le1 := PTree.set inner_bound (Vint (Int.repr (N-1+M))) le) (m1 := memory).
  - constructor; unfold memory_ragged_exit_bound.
    eapply eval_Ebinop with (v1 := Vint (Int.repr (N-1))) (v2 := Vint (Int.repr M)).
    + eapply eval_Ebinop; [constructor; exact NLOOK|constructor|].
      change (Some (Vint (Int.add (Int.repr N) (Int.repr (-1)))) = Some (Vint (Int.repr (N-1)))).
      rewrite rect_integer_add; replace (N + -1) with (N-1) by lia; reflexivity.
    + constructor; exact MLOOK.
    + change (Some (Vint (Int.add (Int.repr (N-1)) (Int.repr M))) = Some (Vint (Int.repr (N-1+M)))).
      rewrite rect_integer_add; reflexivity.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0)
      (le1 := PTree.set column (Vint (Int.repr (N-1+M)))
        (PTree.set inner_bound (Vint (Int.repr (N-1+M))) le)) (m1 := memory); constructor; constructor.
    + apply PTree.gss.
    + rewrite !PTree.gso by congruence; exact NLOOK.
Qed.
Lemma memory_ragged_exit_frame live row column inner_bound N M first second :
  temp_agree live first second ->
  temp_agree live (PTree.set row (Vint (Int.repr N)) (memory_ragged_settle column inner_bound M (N-1) first))
    (PTree.set row (Vint (Int.repr N)) (memory_ragged_settle column inner_bound M (N-1) second)).
Proof.
  unfold memory_ragged_settle; intros FRAME id MEMBER; rewrite !PTree.gsspec.
  destruct (peq id row), (peq id column), (peq id inner_bound); auto.
Qed.

Section SOURCE.
Variable base : rectangle_shape.
Hypothesis VALID : rectangle_layout_valid base.
Variable operations : list named_array_operation.
Hypothesis LAYOUTS : Forall (named_operation_layout base) operations.
Variable row bound column inner_bound parameter : ident.
Variable body outer_body : statement.
Hypothesis RN : row <> bound.
Hypothesis RC : row <> column.
Hypothesis NC : bound <> column.
Hypothesis RK : row <> inner_bound.
Hypothesis NK : bound <> inner_bound.
Hypothesis CK : column <> inner_bound.
Hypothesis MC : parameter <> column.
Hypothesis MK : parameter <> inner_bound.
Hypothesis MR : parameter <> row.
Hypothesis BODY : flatten_region body = map (named_operation_statement row column) operations.
Hypothesis OUTER : flatten_region outer_body = [memory_ragged_setup row parameter inner_bound;
  rectangle_reset column; frontend_counted_loop column inner_bound body].
Variable live : list ident.
Variable pool : list (ident * ident).
Variable candidate : L.stmt.
Variable code : statement.
Hypothesis COMPILE : compile_named_ragged_array_candidate base operations bound parameter live pool candidate = Some code.
Hypothesis CANDIDATE : memory_ragged_candidate_certificate base operations candidate.
Variable width_tree : decision_tree.
Hypothesis LOWER : compile_memory_ragged_width base bound parameter = Some width_tree.

Theorem memory_ragged_array_candidate_local fe ge locals le memory after final N M :
  le ! row = Some (Vint Int.zero) -> le ! bound = Some (Vint (Int.repr N)) ->
  le ! parameter = Some (Vint (Int.repr M)) -> signed_range N -> signed_range M ->
  0 < N <= rectangle_outer_limit base -> 0 < M <= rectangle_stride base -> N+M-1 <= rectangle_stride base ->
  memory_registry_guard_property (named_array_descriptors base operations) (Entry ge locals le memory) ->
  exec_stmt fe ge locals le memory (frontend_counted_loop row bound outer_body) E0 after final Out_normal ->
  exists target, exec_stmt fe ge locals le memory (memory_ragged_candidate code row bound column inner_bound parameter)
    E0 target final Out_normal /\ temp_agree live after target.
Proof.
  intros ZERO NLOOK MLOOK NS MS NB MB WIDTH ALIAS SOURCE.
  set (rows := Z.to_nat N); set (columns := Z.to_nat M).
  assert (RZ : Z.of_nat rows = N) by (unfold rows; apply Z2Nat.id; lia).
  assert (CZ : Z.of_nat columns = M) by (unfold columns; apply Z2Nat.id; lia).
  destruct (@named_array_operations_ragged_source_decode base VALID operations LAYOUTS
    row bound column inner_bound parameter body outer_body RN RC NC RK NK CK MC MK MR BODY OUTER
    fe ge locals le memory after final rows columns ZERO
    ltac:(rewrite RZ; exact NLOOK) ltac:(rewrite CZ; exact MLOOK)
    ltac:(rewrite RZ; exact NS) ltac:(rewrite RZ; exact NB) ltac:(rewrite CZ; lia)
    ltac:(rewrite RZ,CZ; exact WIDTH) SOURCE)
    as [entries [ARRAYS [IDS [POINTERS [LOOP EXIT]]]]].
  destruct ALIAS as [other [OTHER BLOCKS]].
  assert (SAME : map memory_array_block entries = map memory_array_block other).
  { rewrite <- (@memory_descriptor_blocks_binding (named_array_descriptors base operations) entries
      (Entry ge locals le memory) ARRAYS).
    rewrite <- (@memory_descriptor_blocks_binding (named_array_descriptors base operations) other
      (Entry ge locals le memory) OTHER); reflexivity. }
  assert (NONALIAS : GuardMemoryInstr.NonAlias (RuntimeState (memory_array_registry entries) memory))
    by (apply memory_array_registry_nonalias; rewrite SAME; exact BLOCKS).
  rewrite RZ,CZ in LOOP,EXIT.
  pose proof (@CANDIDATE N M (RuntimeState (memory_array_registry entries) memory)
    (RuntimeState (memory_array_registry entries) final) NB MB WIDTH NONALIAS LOOP) as TARGET.
  destruct (@compile_memory_registry_loop_correct (named_array_descriptors base operations) entries fe ge locals ARRAYS
    [bound;parameter] (memory_ragged_positive_bounds base) live pool candidate code [N;M] le
    (RuntimeState (memory_array_registry entries) memory) (RuntimeState (memory_array_registry entries) final) memory
    COMPILE ltac:(apply rectangle_tiled_parameter_view; assumption)
    ltac:(apply memory_ragged_parameter_bounds; lia) TARGET eq_refl)
    as [private_temps [private_memory [VIEW [FRAME EXEC]]]].
  unfold memory_registry_view in VIEW; inversion VIEW; subst private_memory.
  exists (PTree.set row (Vint (Int.repr N)) (memory_ragged_settle column inner_bound M (N-1) private_temps)); split.
  - unfold memory_ragged_candidate; eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact EXEC|].
    apply memory_ragged_restore_execution; auto; rewrite FRAME by (cbn; auto); assumption.
  - rewrite EXIT; apply memory_ragged_exit_frame.
    eapply temp_agree_weaken; [|exact FRAME]; intros id MEMBER; apply in_or_app; right; exact MEMBER.
Qed.

Lemma memory_ragged_named_source_domain fe ge locals le memory after final :
  exec_stmt fe ge locals le memory (frontend_counted_loop row bound outer_body) E0 after final Out_normal ->
  memory_ragged_guard_domain base (named_array_descriptors base operations) row bound parameter (Entry ge locals le memory).
Proof.
  intro SOURCE.
  assert (NORMAL := @memory_ragged_outer_normal row column inner_bound parameter body outer_body
    (@named_array_operations_body_quiet operations row column body BODY) OUTER).
  assert (WRITES := @memory_ragged_outer_writes row column inner_bound parameter body outer_body
    (@named_array_operations_body_writes operations row column body BODY) OUTER).
  assert (DOMAIN := @memory_ragged_source_guard_domain fe ge locals le memory row bound column inner_bound parameter
    body outer_body after final RC RK NC NK RN NORMAL WRITES OUTER SOURCE).
  split; [exact DOMAIN|]; intro ACCEPT.
  unfold memory_ragged_range_accept in ACCEPT; apply andb_true_iff in ACCEPT as [RANGE WIDE].
  destruct (@rectangle_guard_accept_sound base row bound parameter VALID tt (Entry ge locals le memory) DOMAIN RANGE)
    as [ZERO [[ND NR] [MD MRANGE]]].
  pose proof (@memory_ragged_width_sound base bound parameter (Entry ge locals le memory) WIDE) as WIDTH.
  destruct ND as [n NLOOK]; destruct MD as [m MLOOK].
  cbn [entry_temps] in NLOOK,MLOOK,NR,MRANGE,WIDTH; unfold memory_ragged_width_property in WIDTH;
    cbn [entry_temps] in WIDTH; unfold temp_word in NR,MRANGE,WIDTH;
    cbn [entry_temps] in NR,MRANGE,WIDTH; rewrite NLOOK in NR; rewrite MLOOK in MRANGE;
    rewrite NLOOK,MLOOK in WIDTH.
  change (le ! row = Some (Vint Int.zero)) in ZERO.
  set (rows := Z.to_nat (Int.signed n)); set (columns := Z.to_nat (Int.signed m)).
  assert (RZ : Z.of_nat rows = Int.signed n) by (unfold rows; apply Z2Nat.id; lia).
  assert (CZ : Z.of_nat columns = Int.signed m) by (unfold columns; apply Z2Nat.id; lia).
  destruct (@named_array_operations_ragged_source_decode base VALID operations LAYOUTS
    row bound column inner_bound parameter body outer_body RN RC NC RK NK CK MC MK MR BODY OUTER
    fe ge locals le memory after final rows columns ZERO
    ltac:(rewrite RZ,Int.repr_signed; exact NLOOK) ltac:(rewrite CZ,Int.repr_signed; exact MLOOK)
    ltac:(rewrite RZ; apply Int.signed_range) ltac:(rewrite RZ; exact NR) ltac:(rewrite CZ; lia)
    ltac:(rewrite RZ,CZ; exact WIDTH) SOURCE)
    as [entries [ARRAYS [IDS [POINTERS [LOOP EXIT]]]]].
  exists entries; split; assumption.
Qed.
Definition memory_ragged_array_candidate_rule : encoded_private_rule live
  (frontend_counted_loop row bound outer_body) (memory_ragged_candidate code row bound column inner_bound parameter).
Proof.
  assert (OUTER_WRITES := @memory_ragged_outer_writes row column inner_bound parameter body outer_body
    (@named_array_operations_body_writes operations row column body BODY) OUTER).
  assert (WRITES : writes_only [row;inner_bound;column] (frontend_counted_loop row bound outer_body)).
  { assert (OW : writes_only [row;inner_bound;column] outer_body)
      by (eapply writes_only_weaken; [|exact OUTER_WRITES]; cbn; tauto).
    unfold frontend_counted_loop,counter_increment; repeat constructor; cbn; auto. }
  refine {| private_rule_writes := [row;inner_bound;column]; private_rule_source_writes := WRITES;
    private_rule_atoms := unit;
    private_rule_domain := memory_ragged_guard_domain base (named_array_descriptors base operations) row bound parameter;
    private_rule_dimension := memory_ragged_guard_dimension (named_array_descriptors base operations) row bound parameter VALID;
    private_rule_primitives := @memory_ragged_guard_primitives base (named_array_descriptors base operations) row bound parameter width_tree VALID LOWER;
    private_rule_formula := Fact tt |}.
  - intros temps p locals le memory after final RUN.
    exact (@memory_ragged_named_source_domain (adapter_entry temps) (globalenv p) locals le memory after final RUN).
  - intros temps p locals le memory after final SCOPE RUN [RANGE [WIDTH ALIAS]].
    destruct RANGE as [ZERO [[ND NR] [MD MRANGE]]]; destruct ND as [n NLOOK]; destruct MD as [m MLOOK].
    cbn [entry_temps] in NLOOK,MLOOK,NR,MRANGE; unfold memory_ragged_width_property in WIDTH;
      cbn [entry_temps] in WIDTH; unfold temp_word in NR,MRANGE,WIDTH; cbn [entry_temps] in NR,MRANGE,WIDTH; rewrite NLOOK in NR; rewrite MLOOK in MRANGE;
    rewrite NLOOK,MLOOK in WIDTH.
    change (le ! row = Some (Vint Int.zero)) in ZERO.
    destruct (@memory_ragged_array_candidate_local (adapter_entry temps) (globalenv p) locals le memory after final
      (Int.signed n) (Int.signed m) ZERO ltac:(rewrite Int.repr_signed; exact NLOOK)
      ltac:(rewrite Int.repr_signed; exact MLOOK) (Int.signed_range n) (Int.signed_range m) NR MRANGE WIDTH ALIAS RUN)
      as [target [EXEC FRAME]].
    exists target,final; split; [exact EXEC|split; [exact FRAME|apply memory_equivalent_refl]].
Defined.
End SOURCE.
Print Assumptions memory_ragged_array_candidate_local.
Print Assumptions memory_ragged_named_source_domain.
Print Assumptions memory_ragged_array_candidate_rule.
