From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame ClightPureExpr
  ClightStraightLine ClightRectangularStore ClightRectangularLoops ClightLoopExecution
  ClightFrontendLoopProtocol ClightFiniteRegion ClightFrontendRegion ClightLoopSyntax ClightRegionProgress ClightFramedLoop.
From GuardMemory Require Import GuardMemoryParametricSourceClight.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A source execution reaches an actual first body when its two headers are
    active. This service transports the entry frame without interpreting that
    body's addresses, permissions, or optimization assumptions. *)
Lemma memory_parametric_first_inner_body fe ge locals temps memory column inner_bound expression
  upper body outer_body after final stable :
  column <> inner_bound ->
  normal_statement body = true -> writes_only [] body ->
  pure_scalar expression ->
  eval_expr ge locals temps memory expression (Vint (Int.repr upper)) ->
  0 < upper -> signed_range upper ->
  (forall identifier, In identifier stable -> identifier <> column /\ identifier <> inner_bound) ->
  flatten_region outer_body = [memory_parametric_setup inner_bound expression;
    rectangle_reset column;frontend_counted_loop column inner_bound body] ->
  exec_stmt fe ge locals temps memory outer_body E0 after final Out_normal ->
  exists leaf_temps body_after body_final,
    temp_agree stable temps leaf_temps /\
    exec_stmt fe ge locals leaf_temps memory body E0 body_after body_final Out_normal.
Proof.
  intros CK NORMAL WRITES PURE VALUE POSITIVE SAFE PROTECTED OUTER RUN.
  apply flatten_region_execution in RUN; rewrite OUTER in RUN; inversion RUN; subst.
  match goal with SET : exec_stmt _ _ _ _ _ (memory_parametric_setup _ _) _ _ _ _ |- _ =>
    destruct (@memory_parametric_setup_decode fe ge locals temps memory inner_bound expression upper
      _ _ PURE VALUE SET) as [TEMPS MEMORY]; subst end.
  match goal with REST : tail_execution _ _ _ [_;_] _ _ _ _ |- _ => inversion REST; subst end.
  match goal with RESET : exec_stmt _ _ _ _ _ (rectangle_reset _) _ _ _ _ |- _ =>
    destruct (rectangle_reset_decode RESET) as [_ [TEMPS [MEMORY _]]]; subst end.
  match goal with REST : tail_execution _ _ _ [_] _ _ _ _ |- _ => inversion REST; subst end.
  match goal with REST : tail_execution _ _ _ [] _ _ _ _ |- _ => inversion REST; subst end.
  set (prepared := PTree.set column (Vint Int.zero) (PTree.set inner_bound (Vint (Int.repr upper)) temps)) in *.
  assert (TRUE : expression_test (counter_condition column inner_bound) (Entry ge locals prepared memory) true).
  { replace true with (0 <? upper) by (apply Z.ltb_lt; exact POSITIVE).
    apply (@counter_condition_at ge locals prepared memory column inner_bound 0 upper).
    - exact CK.
    - unfold prepared; change (Int.repr 0) with Int.zero; apply PTree.gss.
    - unfold prepared; rewrite PTree.gso by congruence; apply PTree.gss.
    - change (-2147483648 <= 0 <= 2147483647); lia.
    - exact SAFE. }
  assert (FRAME : forall before mem trace next mem',
    exec_stmt fe ge locals before mem body trace next mem' Out_normal ->
    temp_agree [column;inner_bound] before next).
  { intros; eapply structured_temp_frame; [exact WRITES|cbn; tauto|eassumption]. }
  match goal with LOOP : exec_stmt _ _ _ _ _ (frontend_counted_loop _ _ _) _ _ _ _ |- _ =>
    destruct (@frontend_iteration_decode fe ge locals prepared memory column inner_bound body after final TRUE
      (@normal_statement_execution fe ge locals body NORMAL) FRAME LOOP)
      as [next [last [BODY REST]]] end.
  exists prepared,next,last; split; [|exact BODY].
  intros identifier MEMBER; unfold prepared; rewrite !PTree.gso by (specialize (PROTECTED identifier MEMBER); tauto).
  reflexivity.
Qed.

Theorem memory_parametric_source_first_body fe ge locals temps memory row bound column inner_bound expression
  rows upper body outer_body after final stable :
  row <> bound -> row <> column -> row <> inner_bound -> bound <> column -> bound <> inner_bound ->
  column <> inner_bound ->
  normal_statement body = true -> quiet_statement body = true -> writes_only [] body ->
  pure_scalar expression ->
  temps ! row = Some (Vint Int.zero) -> temps ! bound = Some (Vint (Int.repr rows)) ->
  0 < rows -> signed_range rows ->
  eval_expr ge locals temps memory expression (Vint (Int.repr upper)) ->
  0 < upper -> signed_range upper ->
  (forall identifier, In identifier stable -> identifier <> column /\ identifier <> inner_bound) ->
  flatten_region outer_body = [memory_parametric_setup inner_bound expression;
    rectangle_reset column;frontend_counted_loop column inner_bound body] ->
  exec_stmt fe ge locals temps memory (frontend_counted_loop row bound outer_body) E0 after final Out_normal ->
  exists leaf_temps body_after body_final,
    temp_agree stable temps leaf_temps /\
    exec_stmt fe ge locals leaf_temps memory body E0 body_after body_final Out_normal.
Proof.
  intros RN RC RK NC NK CK NORMAL QUIET WRITES PURE ZERO BOUND POSITIVE SAFE
    VALUE INNER_POSITIVE INNER_SAFE PROTECTED OUTER SOURCE.
  assert (TRUE : expression_test (counter_condition row bound) (Entry ge locals temps memory) true).
  { replace true with (0 <? rows) by (apply Z.ltb_lt; exact POSITIVE).
    apply (@counter_condition_at ge locals temps memory row bound 0 rows); auto.
    change (-2147483648 <= 0 <= 2147483647); lia. }
  assert (OUTER_NORMAL : normal_statement outer_body = true)
    by (eapply memory_parametric_outer_normal; eassumption).
  assert (OUTER_WRITES : writes_only [inner_bound;column] outer_body)
    by (eapply memory_parametric_outer_writes; eassumption).
  assert (FRAME : forall before mem trace next mem',
    exec_stmt fe ge locals before mem outer_body trace next mem' Out_normal ->
    temp_agree [row;bound] before next).
  { intros; eapply structured_temp_frame; [exact OUTER_WRITES|cbn; intuition congruence|eassumption]. }
  destruct (@frontend_iteration_decode fe ge locals temps memory row bound outer_body after final TRUE
    (@normal_statement_execution fe ge locals outer_body OUTER_NORMAL) FRAME SOURCE)
    as [next [last [BODY REST]]].
  eapply memory_parametric_first_inner_body;
    [exact CK|exact NORMAL|exact WRITES|exact PURE|exact VALUE|exact INNER_POSITIVE|exact INNER_SAFE|
     exact PROTECTED|exact OUTER|exact BODY].
Qed.

Print Assumptions memory_parametric_source_first_body.
