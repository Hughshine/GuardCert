From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightGuard ClightTempFrame ClightNoWrap ClightStraightLine
  ClightRectangularStore ClightRectangularGuard ClightRectangularLoops ClightFrontendLoopProtocol.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryArrayBackend
  GuardMemoryRegistryBackend GuardMemoryRegistryGuard GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation
  GuardMemoryAffineSourceContext GuardMemoryAffineSourceLoop GuardMemoryParametricSourceClight
  GuardMemoryParametricWidth GuardMemoryParametricGuard GuardMemoryParametricSourceDomain
  GuardMemoryParametricBody.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Section SOURCE.
Variable base : rectangle_shape.
Hypothesis VALID : rectangle_layout_valid base.
Variable row bound column inner_bound : ident.
Variable expression : memory_source_affine.
Variable encoded : L.expr.
Hypothesis ENCODE : memory_source_loop_expression row (memory_source_context row bound expression) expression = Some encoded.
Variable body outer_body : statement.
Variable model : memory_parametric_body_model base row column body.
Let descriptors := parametric_body_descriptors model.
Let instructions := parametric_body_instructions model.
Hypothesis RN : row <> bound.
Hypothesis RC : row <> column.
Hypothesis NC : bound <> column.
Hypothesis RK : row <> inner_bound.
Hypothesis NK : bound <> inner_bound.
Hypothesis CK : column <> inner_bound.
Hypothesis SC : ~ In column (memory_source_affine_parameters row expression).
Hypothesis SK : ~ In inner_bound (memory_source_affine_parameters row expression).
Hypothesis OUTER : flatten_region outer_body =
  [memory_parametric_setup inner_bound (memory_source_affine_code expression); rectangle_reset column;
    frontend_counted_loop column inner_bound body].
Variable bounds : list MemoryNested.A.interval.
Variable width_tree : decision_tree.
Hypothesis LOWER : compile_memory_source_width (rectangle_stride base) row
  (memory_source_context row bound expression) bounds expression = Some width_tree.

Theorem memory_parametric_body_source_domain fe ge locals le memory after final :
  exec_stmt fe ge locals le memory (frontend_counted_loop row bound outer_body) E0 after final Out_normal ->
  memory_source_guard_domain base (descriptors) row bound
    (memory_source_context row bound expression) bounds expression (Entry ge locals le memory).
Proof.
  intro SOURCE.
  assert (NORMAL := @memory_parametric_outer_normal column inner_bound (memory_source_affine_code expression) body outer_body
    (parametric_body_quiet model) OUTER).
  assert (WRITES := @memory_parametric_outer_writes column inner_bound (memory_source_affine_code expression) body outer_body
    (parametric_body_writes model) OUTER).
  destruct (@memory_parametric_source_words fe ge locals le memory row bound column inner_bound expression body outer_body
    after final RN RC RK NC NK CK NORMAL WRITES OUTER SOURCE) as [ROW [BOUND WORDS]].
  assert (PARAMETERS : memory_source_header_accept base row bound (Entry ge locals le memory) = true ->
    MemoryNested.A.typed_view (memory_source_context row bound expression)
      (memory_source_parameter_values (memory_source_context row bound expression) (Entry ge locals le memory)) le).
  { intro HEADER.
    destruct (@memory_source_header_sound base row bound (Entry ge locals le memory) VALID ROW BOUND HEADER)
      as [ZERO [_ NRANGE]].
    apply memory_source_parameter_view; intros identifier MEMBER.
    apply memory_source_context_member in MEMBER; destruct MEMBER as [->|MEMBER]; [exact BOUND|].
    apply WORDS; [exact ZERO|exact (proj1 NRANGE)|exact MEMBER]. }
  split; [exact ROW|]; split; [exact BOUND|]; split; [exact PARAMETERS|].
  intros HEADER RANGES WIDTH.
  destruct (@memory_source_header_sound base row bound (Entry ge locals le memory) VALID ROW BOUND HEADER)
    as [ZERO [ND NRANGE]].
  pose proof (PARAMETERS HEADER) as VIEW.
  assert (WITHIN : MemoryNested.A.env_within bounds
    (memory_source_parameter_values (memory_source_context row bound expression) (Entry ge locals le memory))).
  { eapply MemorySourceRanges.range_guard_sound with
      (layout := memory_source_context row bound expression) (s := Entry ge locals le memory);
      [exact VIEW|apply memory_source_range_exact; [exact VIEW|symmetry; exact RANGES]]. }
  set (valuation := fun identifier => Int.signed (temp_word identifier le)).
  assert (WIDE : 0 < memory_source_affine_math (memory_source_set_valuation valuation row 0) expression /\
    forall value, 0 <= value < valuation bound ->
      0 <= memory_source_affine_math (memory_source_set_valuation valuation row value) expression <= rectangle_stride base).
  { eapply (@compile_memory_source_width_sound (rectangle_stride base) row bound
      (memory_source_other_parameters row bound expression) bounds expression width_tree valuation ge locals le memory);
      [exact (proj1 NRANGE)|exact LOWER|exact VIEW|exact WITHIN|].
    apply (proj2 (@memory_source_width_exact (rectangle_stride base) row
      (memory_source_context row bound expression) bounds expression width_tree (Entry ge locals le memory) LOWER VIEW WITHIN true)).
    symmetry; exact WIDTH. }
  destruct ND as [n NLOOK].
  change (le ! bound = Some (Vint n)) in NLOOK.
  cbn [entry_temps] in ZERO,NRANGE.
  assert (NVALUE : valuation bound = Int.signed n) by (unfold valuation,temp_word; rewrite NLOOK; reflexivity).
  set (rows := Z.to_nat (Int.signed n)).
  assert (RZ : Z.of_nat rows = Int.signed n).
  { unfold rows; apply Z2Nat.id; rewrite <- NVALUE; exact (Z.lt_le_incl _ _ (proj1 NRANGE)). }
  assert (CONTEXT : map valuation (memory_source_context row bound expression) =
    Z.of_nat rows::map valuation (memory_source_other_parameters row bound expression)).
  { unfold memory_source_context; cbn; rewrite NVALUE,RZ; reflexivity. }
  assert (PARAM_WORDS : forall identifier, In identifier (memory_source_affine_parameters row expression) ->
    le ! identifier = Some (Vint (Int.repr (valuation identifier)))).
  { intros identifier MEMBER; apply memory_source_affine_parameter_member in MEMBER.
    destruct (WORDS ZERO (proj1 NRANGE) identifier (proj1 MEMBER)) as [word LOOK].
    cbn [entry_temps] in LOOK; unfold valuation,temp_word; rewrite LOOK,Int.repr_signed; reflexivity. }
  destruct (@memory_parametric_body_source_decode base VALID row bound column inner_bound expression
    (memory_source_context row bound expression) encoded ENCODE body outer_body model RN RC NC RK NK CK SC SK OUTER
    fe ge locals le memory after final rows (map valuation (memory_source_other_parameters row bound expression)) valuation
    ZERO ltac:(rewrite RZ,Int.repr_signed; exact NLOOK) PARAM_WORDS CONTEXT
    ltac:(rewrite RZ; apply Int.signed_range) ltac:(rewrite RZ,<- NVALUE; exact NRANGE)
    ltac:(intros i I; pose proof (@memory_source_loop_expression_value expression row
      (memory_source_context row bound expression) encoded valuation i ENCODE) as SAME;
      change (L.eval_expr (i::valuation bound::map valuation (memory_source_other_parameters row bound expression)) encoded =
        memory_source_affine_math (memory_source_set_valuation valuation row i) expression) in SAME;
      rewrite NVALUE,<- RZ in SAME; rewrite SAME;
      apply (proj2 WIDE); rewrite NVALUE,<- RZ; exact I)
    ltac:(pose proof (@memory_source_loop_expression_value expression row
      (memory_source_context row bound expression) encoded valuation 0 ENCODE) as SAME;
      change (L.eval_expr (0::valuation bound::map valuation (memory_source_other_parameters row bound expression)) encoded =
        memory_source_affine_math (memory_source_set_valuation valuation row 0) expression) in SAME;
      rewrite NVALUE,<- RZ in SAME; rewrite SAME; exact (proj1 WIDE)) SOURCE)
    as [entries [ARRAYS [UNIQUE [POINTERS REST]]]].
  exists entries; split; assumption.
Qed.
End SOURCE.
Print Assumptions memory_parametric_body_source_domain.
