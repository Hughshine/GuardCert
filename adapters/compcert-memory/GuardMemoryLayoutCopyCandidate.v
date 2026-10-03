From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import AbstractGuard SemanticFacts CompCertMemoryEquivalence
  ClightGuard ClightCondition ClightNoWrap ClightTempFrame ClightStraightLine ClightCountedLoop ClightLoopSyntax
  ClightRectangularStore ClightRectangularGuard ClightRectangularLoops ClightFrontendLoopProtocol
  ClightPrivateRule ClightProjectedExecution ClightTempFootprint.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryArrayBackend
  GuardMemoryMultipleArrays GuardMemoryRegistryBackend GuardMemoryRegistryGuard GuardMemoryNamedOperations
  GuardMemoryNamedRegistrySource GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation
  GuardMemoryAffineSourceContext GuardMemoryAffineSourceLoop GuardMemoryParametricLoops GuardMemoryParametricSourceClight
  GuardMemoryNamedParametricSource GuardMemoryParametricWidth GuardMemoryParametricGuard
  GuardMemoryParametricSourceDomain GuardMemoryParametricChecker GuardMemoryParametricRestore GuardMemoryParametricCandidate
  GuardMemoryCommonLayout GuardMemoryLayoutCopy GuardMemoryLayoutCopyInstruction GuardMemoryLayoutCopyRegistry
  GuardMemoryLayoutCopySource GuardMemoryLayoutCopyDomain GuardMemoryParametricInstructionChecker.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Section SOURCE.
Variable write_shape read_shape : rectangle_shape.
Hypothesis WVALID : rectangle_layout_valid write_shape.
Hypothesis RVALID : rectangle_layout_valid read_shape.
Variable write_array read_array : ident.
Hypothesis DISTINCT : write_array <> read_array.
Let base := memory_common_layout write_shape read_shape.
Let VALID : rectangle_layout_valid base := memory_common_layout_valid WVALID RVALID.
Let descriptors := memory_layout_copy_descriptors write_shape read_shape write_array read_array.
Let instructions := [memory_layout_copy_instruction write_shape read_shape write_array read_array].
Variable row bound column inner_bound : ident.
Variable expression : memory_source_affine.
Variable encoded : L.expr.
Hypothesis ENCODE : memory_source_loop_expression row (memory_source_context row bound expression) expression = Some encoded.
Variable body outer_body : statement.
Hypothesis RN : row <> bound.
Hypothesis RC : row <> column.
Hypothesis NC : bound <> column.
Hypothesis RK : row <> inner_bound.
Hypothesis NK : bound <> inner_bound.
Hypothesis CK : column <> inner_bound.
Hypothesis SC : ~ In column (memory_source_affine_parameters row expression).
Hypothesis SK : ~ In inner_bound (memory_source_affine_parameters row expression).
Hypothesis BODY : flatten_region body = [memory_layout_copy_statement write_shape read_shape write_array read_array row column].
Hypothesis OUTER : flatten_region outer_body =
  [memory_parametric_setup inner_bound (memory_source_affine_code expression); rectangle_reset column;
    frontend_counted_loop column inner_bound body].
Variable bounds : list MemoryNested.A.interval.
Variable live : list ident.
Variable pool : list (ident*ident).
Variable candidate : L.stmt.
Variable code : statement.
Hypothesis COMPILE : compile_memory_registry_loop descriptors (memory_source_context row bound expression) bounds live pool candidate = Some code.
Hypothesis CANDIDATE : memory_parametric_instruction_candidate_certificate base instructions row
  (memory_source_context row bound expression) bounds expression encoded candidate.
Variable width_tree : decision_tree.
Hypothesis LOWER : compile_memory_source_width (rectangle_stride base) row
  (memory_source_context row bound expression) bounds expression = Some width_tree.

Theorem memory_layout_copy_candidate_local fe ge locals le memory after final :
  memory_source_guard_accept base descriptors row bound
    (memory_source_context row bound expression) bounds expression (Entry ge locals le memory) = true ->
  exec_stmt fe ge locals le memory (frontend_counted_loop row bound outer_body) E0 after final Out_normal ->
  exists target, exec_stmt fe ge locals le memory
    (memory_parametric_candidate code row bound column inner_bound expression) E0 target final Out_normal /\
    temp_agree live after target.
Proof.
  intros ACCEPT SOURCE.
  pose proof (@memory_layout_copy_source_domain write_shape read_shape WVALID RVALID write_array read_array DISTINCT row bound column inner_bound expression encoded ENCODE
    body outer_body RN RC NC RK NK CK SC SK BODY OUTER bounds width_tree LOWER fe ge locals le memory after final SOURCE) as DOMAIN.
  pose proof (@memory_source_guard_sound base descriptors row bound
    (memory_source_other_parameters row bound expression) bounds expression width_tree (Entry ge locals le memory)
    VALID LOWER DOMAIN ACCEPT) as PROPERTY.
  destruct PROPERTY as [ZERO [[ND NRANGE] [WITHIN [[FIRST WIDTH] ALIAS]]]].
  assert (HEADER : memory_source_header_accept base row bound (Entry ge locals le memory) = true).
  { unfold memory_source_guard_accept in ACCEPT; repeat rewrite andb_true_iff in ACCEPT; tauto. }
  assert (WIDTH_FLAG : memory_source_width_accept (rectangle_stride base) row
    (memory_source_context row bound expression) expression (Entry ge locals le memory) = true).
  { unfold memory_source_guard_accept in ACCEPT; repeat rewrite andb_true_iff in ACCEPT; tauto. }
  pose proof (proj1 (proj2 (proj2 DOMAIN)) HEADER) as VIEW.
  set (valuation := fun identifier => Int.signed (temp_word identifier le)).
  set (N := valuation bound).
  set (parameters := map valuation (memory_source_other_parameters row bound expression)).
  assert (CONTEXT : map valuation (memory_source_context row bound expression) = N::parameters) by reflexivity.
  assert (PARAM_WORDS : forall identifier, In identifier (memory_source_affine_parameters row expression) ->
    le ! identifier = Some (Vint (Int.repr (valuation identifier)))).
  { intros identifier MEMBER; apply memory_source_affine_parameter_member in MEMBER.
    destruct (@memory_source_typed_word (memory_source_context row bound expression)
      (memory_source_parameter_values (memory_source_context row bound expression) (Entry ge locals le memory)) le identifier VIEW
      ltac:(apply memory_source_context_read; tauto)) as [word WORD].
    unfold valuation,temp_word; rewrite WORD,Int.repr_signed; reflexivity. }
  destruct ND as [n NLOOK].
  change (le ! bound = Some (Vint n)) in NLOOK.
  assert (NVALUE : N = Int.signed n) by (unfold N,valuation,temp_word; rewrite NLOOK; reflexivity).
  cbn [entry_temps] in ZERO,NRANGE,WIDTH,FIRST.
  change (0 < N <= rectangle_outer_limit base) in NRANGE.
  set (rows := Z.to_nat N).
  assert (RZ : Z.of_nat rows = N) by (unfold rows; apply Z2Nat.id; lia).
  assert (VALUE : forall i, L.eval_expr (i::N::parameters) encoded =
    memory_source_affine_math (memory_source_set_valuation valuation row i) expression).
  { intro i; exact (@memory_source_loop_expression_value expression row
      (memory_source_context row bound expression) encoded valuation i ENCODE). }
  destruct (@memory_layout_copy_source_decode write_shape read_shape WVALID RVALID write_array read_array DISTINCT row bound column inner_bound expression
    (memory_source_context row bound expression) encoded ENCODE body outer_body RN RC NC RK NK CK SC SK BODY OUTER
    fe ge locals le memory after final rows parameters valuation
    ZERO ltac:(rewrite RZ,NVALUE,Int.repr_signed; exact NLOOK) PARAM_WORDS ltac:(rewrite RZ; exact CONTEXT)
    ltac:(rewrite RZ,NVALUE; apply Int.signed_range) ltac:(rewrite RZ; exact NRANGE)
    ltac:(rewrite RZ; intros i I; rewrite VALUE; apply WIDTH; exact I)
    ltac:(rewrite RZ,VALUE; exact FIRST) SOURCE)
    as [entries [ARRAYS [IDS [POINTERS [LOOP EXIT]]]]].
  destruct ALIAS as [other [OTHER BLOCKS]].
  assert (SAME : map memory_array_block entries = map memory_array_block other).
  { rewrite <- (@memory_descriptor_blocks_binding descriptors entries (Entry ge locals le memory) ARRAYS).
    rewrite <- (@memory_descriptor_blocks_binding descriptors other (Entry ge locals le memory) OTHER); reflexivity. }
  assert (NONALIAS : GuardMemoryInstr.NonAlias (RuntimeState (memory_array_registry entries) memory))
    by (apply memory_array_registry_nonalias; rewrite SAME; exact BLOCKS).
  rewrite RZ in LOOP,EXIT.
  pose proof (@CANDIDATE (N::parameters) (RuntimeState (memory_array_registry entries) memory)
    (RuntimeState (memory_array_registry entries) final)
    ltac:(rewrite <- CONTEXT,map_length; reflexivity) WITHIN WIDTH_FLAG NONALIAS LOOP) as TARGET.
  destruct (@compile_memory_registry_loop_correct descriptors entries fe ge locals ARRAYS
    (memory_source_context row bound expression) bounds live pool candidate code (N::parameters) le
    (RuntimeState (memory_array_registry entries) memory) (RuntimeState (memory_array_registry entries) final) memory
    COMPILE VIEW WITHIN TARGET eq_refl) as [private_temps [private_memory [MEMORY [FRAME EXEC]]]].
  unfold memory_registry_view in MEMORY; inversion MEMORY; subst private_memory.
  set (upper := fun i => memory_source_affine_math (memory_source_set_valuation valuation row i) expression).
  exists (PTree.set row (Vint (Int.repr N)) (memory_parametric_settle column inner_bound upper (N-1) private_temps)); split.
  - unfold memory_parametric_candidate; eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact EXEC|].
    apply memory_parametric_restore_execution; auto.
    + rewrite FRAME by (apply in_or_app; left; unfold memory_source_context; cbn; auto).
      rewrite NVALUE,Int.repr_signed; exact NLOOK.
    + intros identifier MEMBER; rewrite FRAME by (apply in_or_app; left; apply memory_source_context_read;
        apply memory_source_affine_parameter_member in MEMBER; tauto).
      apply PARAM_WORDS; exact MEMBER.
  - rewrite EXIT; unfold memory_parametric_settle,upper; rewrite VALUE.
    assert (SMALL : temp_agree live le private_temps).
    { eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER; apply in_or_app; right; exact MEMBER. }
    exact (@memory_parametric_exit_frame live row column inner_bound N
      (fun i => memory_source_affine_math (memory_source_set_valuation valuation row i) expression) le private_temps SMALL).
Qed.

Definition memory_layout_copy_candidate_rule : encoded_private_rule live
  (frontend_counted_loop row bound outer_body) (memory_parametric_candidate code row bound column inner_bound expression).
Proof.
  assert (OUTER_WRITES := @memory_parametric_outer_writes column inner_bound (memory_source_affine_code expression) body outer_body
    (@memory_layout_copy_body_writes write_shape read_shape write_array read_array row column body BODY) OUTER).
  assert (WRITES : writes_only [row;inner_bound;column] (frontend_counted_loop row bound outer_body)).
  { assert (OW : writes_only [row;inner_bound;column] outer_body)
      by (eapply writes_only_weaken; [|exact OUTER_WRITES]; cbn; tauto).
    unfold frontend_counted_loop,counter_increment; repeat constructor; cbn; auto. }
  refine {| private_rule_writes := [row;inner_bound;column]; private_rule_source_writes := WRITES;
    private_rule_atoms := unit;
    private_rule_domain := memory_source_guard_domain base descriptors row bound
      (memory_source_context row bound expression) bounds expression;
    private_rule_dimension := memory_source_guard_dimension base descriptors row bound
      (memory_source_context row bound expression) bounds expression;
    private_rule_primitives := @memory_source_guard_primitives base descriptors row bound
      (memory_source_context row bound expression) bounds expression width_tree LOWER;
    private_rule_formula := Fact tt |}.
  - intros temps p locals le memory after final RUN.
    exact (@memory_layout_copy_source_domain write_shape read_shape WVALID RVALID write_array read_array DISTINCT row bound column inner_bound expression encoded ENCODE
      body outer_body RN RC NC RK NK CK SC SK BODY OUTER bounds width_tree LOWER
      (adapter_entry temps) (globalenv p) locals le memory after final RUN).
  - intros temps p locals le memory after final SCOPE RUN ACCEPT.
    destruct (@memory_layout_copy_candidate_local (adapter_entry temps) (globalenv p) locals le memory after final ACCEPT RUN)
      as [target [EXEC FRAME]].
    exists target,final; split; [exact EXEC|split; [exact FRAME|apply memory_equivalent_refl]].
Defined.
End SOURCE.
Print Assumptions memory_layout_copy_candidate_local.
Print Assumptions memory_layout_copy_candidate_rule.
