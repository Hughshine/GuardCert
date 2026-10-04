From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightTempFrame ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRectangles GuardMemoryFiniteAliasCondition GuardMemoryFootprintCapabilities
  GuardMemoryAffineSourceExpressions GuardMemoryBooleanScan GuardMemoryPointerCellComparison GuardMemoryWindowCells.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestValuation AffineNestMathDomain
  AffineNestScanModel AffineNestScanSyntax AffineNestScanNamespace AffineNestScanNamedExecution
  AffineNestScanAddress AffineNestScanPairTest.
Import ListNotations.
Set Implicit Arguments.

Definition affine_scan_pair_statement nest left right flag lower first second first_expression second_expression :=
  affine_scan_statement nest left(affine_scan_values nest left) lower
    (affine_scan_statement nest right(affine_scan_values nest right) lower
      (memory_boolean_test_body flag(memory_pointer_cells_test
        (affine_scan_address first(affine_scan_values nest left) first_expression)
        (affine_scan_address second(affine_scan_values nest right) second_expression)))).
Definition affine_scan_pair_result nest valuation lower locations first second first_expression second_expression :=
  affine_scan_result nest valuation lower(fun first_point=>affine_scan_result nest valuation lower(fun second_point=>
    memory_cell_pair_address_check locations
      (point_cell first(memory_source_affine_math first_point first_expression))
      (point_cell second(memory_source_affine_math second_point second_expression)))).

Theorem affine_scan_pair_execution iterator bound expression body child parameters live left right flag
  (left_names:affine_scan_namespace(AffineSourceAxis iterator bound expression body child) parameters live left flag)
  (right_names:affine_scan_namespace(AffineSourceAxis iterator bound expression body child) parameters
    (map left(affine_nest_controls(AffineSourceAxis iterator bound expression body child))++live) right flag)
  fe ge locals original current memory valuation lower accepted bounds layout window_lower window_upper
  first second first_expression second_expression :
  let nest:=AffineSourceAxis iterator bound expression body child in
  affine_nest_bound_dependencies [] parameters nest -> incl parameters live -> In iterator live ->
  In first live -> In second live -> first<>second ->
  signed_range window_lower -> signed_range(window_upper-1) ->
  affine_math_domain bounds layout nest valuation lower -> affine_word_view parameters valuation original ->
  original!iterator=Some(Vint(Int.repr lower)) -> temp_agree live original current ->
  current!flag=Some(memory_boolean_word accepted) ->
  (forall identifier, In identifier(memory_source_affine_reads first_expression) -> In identifier(affine_nest_iterators nest++parameters)) ->
  (forall identifier, In identifier(memory_source_affine_reads second_expression) -> In identifier(affine_nest_iterators nest++parameters)) ->
  (forall point, affine_scan_point nest valuation lower point ->
    memory_cell_capable(window_multi_pointer_locations original window_lower window_upper) memory
      (point_cell first(memory_source_affine_math point first_expression)) /\
    memory_cell_capable(window_multi_pointer_locations original window_lower window_upper) memory
      (point_cell second(memory_source_affine_math point second_expression))) ->
  exists after,
    exec_stmt fe ge locals current memory
      (affine_scan_pair_statement nest left right flag(Etempvar iterator type_int32s) first second first_expression second_expression)
      E0 after memory Out_normal /\ temp_agree live current after /\
    after!flag=Some(memory_boolean_word(accepted&&affine_scan_pair_result nest valuation lower
      (window_multi_pointer_locations original window_lower window_upper) first second first_expression second_expression)).
Proof.
  cbn zeta.
  intros DEPENDENCIES PARAM_PUBLIC ROOT FIRST_PUBLIC SECOND_PUBLIC DISTINCT LOW HIGH DOMAIN WORDS ROOT_WORD FRAME FLAG FIRST_READS SECOND_READS CAPABLE.
  unfold affine_scan_pair_statement,affine_scan_pair_result.
  set(nest:=AffineSourceAxis iterator bound expression body child) in *.
  set(protected_left:=map left(affine_nest_controls nest)++live) in *.
  set(locations:=window_multi_pointer_locations original window_lower window_upper) in *.
  eapply affine_scan_named_execution with(names:=left_names)(valuation:=valuation)(original:=original)
    (bounds:=bounds)(layout:=layout)
    (test:=fun first_point=>affine_scan_result nest valuation lower(fun second_point=>
      memory_cell_pair_address_check locations
        (point_cell first(memory_source_affine_math first_point first_expression))
        (point_cell second(memory_source_affine_math second_point second_expression)))); try eassumption.
  - constructor; rewrite FRAME by exact ROOT; exact ROOT_WORD.
  - intros first_point outer good protected FIRST_POINT LEFT_WORDS OUTER_FRAME GOOD PROTECTED INCLUDED.
    assert(RIGHT_WORDS:affine_word_view parameters valuation outer).
    { eapply affine_word_view_frame; [exact WORDS|].
      eapply temp_agree_weaken; [exact PARAM_PUBLIC|exact OUTER_FRAME]. }
    assert(INNER:exists after,
      exec_stmt fe ge locals outer memory
        (affine_scan_statement nest right(affine_scan_values nest right)(Etempvar iterator type_int32s)
          (memory_boolean_test_body flag(memory_pointer_cells_test
            (affine_scan_address first(affine_scan_values nest left) first_expression)
            (affine_scan_address second(affine_scan_values nest right) second_expression)))) E0 after memory Out_normal /\
      temp_agree protected_left outer after /\
      after!flag=Some(memory_boolean_word(good&&affine_scan_result nest valuation lower(fun second_point=>
        memory_cell_pair_address_check locations
          (point_cell first(memory_source_affine_math first_point first_expression))
          (point_cell second(memory_source_affine_math second_point second_expression)))))).
    { eapply affine_scan_named_execution with(names:=right_names)(valuation:=valuation)(original:=outer)
        (bounds:=bounds)(layout:=layout); try eassumption.
      - intros identifier MEMBER; unfold protected_left; apply in_or_app; right; apply PARAM_PUBLIC; exact MEMBER.
      - apply temp_agree_refl.
      - constructor; rewrite OUTER_FRAME by exact ROOT; exact ROOT_WORD.
      - intros second_point inside before keep SECOND_POINT INSIDE_WORDS INSIDE_FRAME BEFORE KEEP KEEP_INCLUDED.
        apply memory_boolean_test_body_execution; [exact KEEP|exact BEFORE|].
        eapply affine_scan_pair_test with(original:=original)(first_value:=first_point)(second_value:=second_point);
          try eassumption.
        + rewrite INSIDE_FRAME by(unfold protected_left; apply in_or_app; right; exact FIRST_PUBLIC).
          apply OUTER_FRAME; exact FIRST_PUBLIC.
        + rewrite INSIDE_FRAME by(unfold protected_left; apply in_or_app; right; exact SECOND_PUBLIC).
          apply OUTER_FRAME; exact SECOND_PUBLIC.
        + intros identifier MEMBER; rewrite INSIDE_FRAME.
          * apply LEFT_WORDS,FIRST_READS; exact MEMBER.
          * apply FIRST_READS in MEMBER; apply in_app_or in MEMBER as [COORDINATE|PARAMETER].
            -- rewrite affine_scan_values_iterator by exact COORDINATE; unfold protected_left.
               apply in_or_app; left; apply in_map,affine_nest_controls_member; auto.
            -- rewrite(affine_scan_names_parameters left_names identifier PARAMETER); unfold protected_left.
               apply in_or_app; right; apply PARAM_PUBLIC; exact PARAMETER.
        + intros identifier MEMBER; apply INSIDE_WORDS,SECOND_READS; exact MEMBER.
        + exact(proj1(CAPABLE first_point FIRST_POINT)).
        + exact(proj2(CAPABLE second_point SECOND_POINT)). }
    destruct INNER as [after [RUN [AFTER RESULT]]]; exists after; split; [exact RUN|].
    split; [eapply temp_agree_weaken; [exact INCLUDED|exact AFTER]|exact RESULT].
Qed.
Print Assumptions affine_scan_pair_execution.
