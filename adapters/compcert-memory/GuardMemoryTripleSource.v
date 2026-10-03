From Stdlib Require Import List ZArith Lia Bool.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame ClightLoopSyntax
  ClightPureExpr ClightStraightLine ClightFiniteRegion ClightRegionProgress ClightFrontendLoopProtocol
  ClightRectangularStore ClightRectangularLoops.
From GuardMemory Require Import GuardMemorySettledCountedLoop GuardMemoryControlSettle.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma memory_reset_child_decode fe ge locals code iterator child temps memory after final :
  flatten_region code = [rectangle_reset iterator;child] ->
  exec_stmt fe ge locals temps memory code E0 after final Out_normal ->
  exec_stmt fe ge locals (PTree.set iterator (Vint Int.zero) temps) memory child E0 after final Out_normal.
Proof.
  intros FLAT RUN; apply flatten_region_execution in RUN; rewrite FLAT in RUN.
  inversion RUN; subst.
  match goal with RESET : exec_stmt _ _ _ _ _ (rectangle_reset _) _ _ _ _ |- _ =>
    inversion RESET; subst;
    match goal with EVAL : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ => apply scalar_const_inv in EVAL; subst end end.
  match goal with CHILD : tail_execution _ _ _ [child] _ _ _ _ |- _ =>
    inversion CHILD; subst;
    match goal with END : tail_execution _ _ _ [] _ _ _ _ |- _ => inversion END; subst end end.
  assumption.
Qed.
Lemma memory_reset_child_writes body iterator child allowed :
  flatten_region body = [rectangle_reset iterator;child] ->
  In iterator allowed -> writes_only allowed child -> writes_only allowed body.
Proof.
  intros FLAT MEMBER WRITES; apply flatten_writes_certificate; rewrite FLAT.
  constructor; [constructor; exact MEMBER|constructor; [exact WRITES|constructor]].
Qed.
Lemma memory_reset_child_quiet body iterator child :
  flatten_region body = [rectangle_reset iterator;child] -> quiet_statement child = true -> quiet_statement body = true.
Proof.
  intros FLAT QUIET; apply flatten_quiet_certificate; rewrite FLAT; repeat constructor; exact QUIET.
Qed.
Lemma memory_frontend_loop_quiet iterator bound body : quiet_statement body = true ->
  quiet_statement (frontend_counted_loop iterator bound body) = true.
Proof.
  intro QUIET; unfold frontend_counted_loop,counter_increment; cbn [quiet_statement]; rewrite QUIET; reflexivity.
Qed.
Lemma memory_frontend_loop_writes iterator bound body allowed :
  In iterator allowed -> writes_only allowed body -> writes_only allowed (frontend_counted_loop iterator bound body).
Proof.
  intros MEMBER WRITES; unfold frontend_counted_loop,counter_increment; repeat constructor; auto.
Qed.
Print Assumptions memory_reset_child_decode.

Theorem memory_triple_inner_decode fe ge locals row column depth depth_bound body
  (point : Z -> Z -> Z -> mem -> mem -> Prop) count i j temps memory after final :
  depth <> row -> depth <> column -> depth <> depth_bound ->
  normal_statement body = true -> writes_only [] body -> signed_range (Z.of_nat count) ->
  (forall k le before next target, 0 <= k < Z.of_nat count ->
    le ! row = Some (Vint (Int.repr i)) -> le ! column = Some (Vint (Int.repr j)) ->
    le ! depth = Some (Vint (Int.repr k)) ->
    exec_stmt fe ge locals le before body E0 next target Out_normal ->
    point i j k before target /\ next = le) ->
  temps ! row = Some (Vint (Int.repr i)) -> temps ! column = Some (Vint (Int.repr j)) ->
  temps ! depth = Some (Vint Int.zero) -> temps ! depth_bound = Some (Vint (Int.repr (Z.of_nat count))) ->
  exec_stmt fe ge locals temps memory (frontend_counted_loop depth depth_bound body) E0 after final Out_normal ->
  counted_iterations (point i j) count 0 memory final /\
    after = PTree.set depth (Vint (Int.repr (Z.of_nat count))) temps.
Proof.
  intros DR DC DB NORMAL WRITES RANGE POINT ROW COLUMN ZERO BOUND RUN.
  assert (EXIT : PTree.set depth (Vint (Int.repr (Z.of_nat count))) temps =
    settled_exit (fun le => le) depth temps count (Z.of_nat count)) by (destruct count; reflexivity).
  rewrite EXIT.
  eapply frontend_settled_decode with (written := []) (settle := fun le => le)
    (body := body) (floor := 0) (stable := [row;column;depth_bound]) (base := temps).
  - intros; reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - exact DB.
  - split; cbn; tauto.
  - cbn; intuition congruence.
  - cbn; tauto.
  - exact NORMAL.
  - exact WRITES.
  - exact RANGE.
  - intros k le before next target K DEPTH BOUND' FRAME EXEC.
    eapply POINT; [exact K| | |exact DEPTH|exact EXEC].
    + rewrite (FRAME row ltac:(cbn; auto)); exact ROW.
    + rewrite (FRAME column ltac:(cbn; auto)); exact COLUMN.
  - lia.
  - unfold signed_range; change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia.
  - lia.
  - exact ZERO.
  - exact BOUND.
  - apply temp_agree_refl.
  - exact RUN.
Qed.
Print Assumptions memory_triple_inner_decode.

Theorem memory_triple_middle_decode fe ge locals row column column_bound depth depth_bound body middle_body
  (point : Z -> Z -> Z -> mem -> mem -> Prop) columns depths i temps memory after final :
  depth <> row -> depth <> column -> depth <> depth_bound -> depth <> column_bound ->
  column <> row -> column <> column_bound -> column <> depth_bound ->
  normal_statement body = true -> quiet_statement body = true -> writes_only [] body ->
  signed_range (Z.of_nat columns) -> signed_range (Z.of_nat depths) -> columns <> O ->
  flatten_region middle_body = [rectangle_reset depth;frontend_counted_loop depth depth_bound body] ->
  (forall j k le before next target, 0 <= j < Z.of_nat columns -> 0 <= k < Z.of_nat depths ->
    le ! row = Some (Vint (Int.repr i)) -> le ! column = Some (Vint (Int.repr j)) ->
    le ! depth = Some (Vint (Int.repr k)) ->
    exec_stmt fe ge locals le before body E0 next target Out_normal ->
    point i j k before target /\ next = le) ->
  temps ! row = Some (Vint (Int.repr i)) -> temps ! column = Some (Vint Int.zero) ->
  temps ! column_bound = Some (Vint (Int.repr (Z.of_nat columns))) ->
  temps ! depth_bound = Some (Vint (Int.repr (Z.of_nat depths))) ->
  exec_stmt fe ge locals temps memory (frontend_counted_loop column column_bound middle_body) E0 after final Out_normal ->
  counted_iterations (fun j => counted_iterations (point i j) depths 0) columns 0 memory final /\
  after = PTree.set column (Vint (Int.repr (Z.of_nat columns)))
    (PTree.set depth (Vint (Int.repr (Z.of_nat depths))) temps).
Proof.
  intros DR DC DB DCB CR CCB CDB NORMAL QUIET WRITES CRANGE DRANGE POSITIVE MIDDLE POINT ROW ZERO CBOUND DBOUND RUN.
  set (assignments := [(depth,Vint (Int.repr (Z.of_nat depths)))]).
  assert (EXIT : PTree.set column (Vint (Int.repr (Z.of_nat columns)))
    (PTree.set depth (Vint (Int.repr (Z.of_nat depths))) temps) =
    settled_exit (memory_settle_controls assignments) column temps columns (Z.of_nat columns)).
  { destruct columns; [contradiction|reflexivity]. }
  rewrite EXIT.
  assert (MQUIET : quiet_statement middle_body = true).
  { eapply memory_reset_child_quiet; [exact MIDDLE|apply memory_frontend_loop_quiet; exact QUIET]. }
  assert (MNORMAL : normal_statement middle_body = true).
  { apply flatten_normal_certificate; rewrite MIDDLE; constructor; [reflexivity|].
    constructor; [change (quiet_statement (frontend_counted_loop depth depth_bound body) = true);
      apply memory_frontend_loop_quiet; exact QUIET|constructor]. }
  assert (MWRITES : writes_only [depth] middle_body).
  { eapply memory_reset_child_writes; [exact MIDDLE|cbn; auto|].
    apply memory_frontend_loop_writes; [cbn; auto|].
    eapply writes_only_weaken with (small := []); [cbn; tauto|exact WRITES]. }
  eapply frontend_settled_decode with (written := [depth]) (settle := memory_settle_controls assignments)
    (body := middle_body) (floor := 0) (stable := [row;depth_bound]) (base := temps).
  - intros le key FRESH; apply memory_settle_controls_frame; exact FRESH.
  - intro le; apply memory_settle_controls_idempotent.
  - intros le value; apply memory_settle_controls_commute; unfold assignments; cbn; intuition congruence.
  - exact CCB.
  - split; cbn; intuition congruence.
  - cbn; intuition congruence.
  - intros identifier MEMBER; cbn in *; intuition congruence.
  - exact MNORMAL.
  - exact MWRITES.
  - exact CRANGE.
  - intros j le before next target J COLUMN CBOUND' FRAME EXEC.
    pose proof (@memory_reset_child_decode fe ge locals middle_body depth
      (frontend_counted_loop depth depth_bound body) le before next target MIDDLE EXEC) as INNER.
    destruct (@memory_triple_inner_decode fe ge locals row column depth depth_bound body point depths i j
      (PTree.set depth (Vint Int.zero) le) before next target DR DC DB NORMAL WRITES DRANGE
      ltac:(intros k current initial final_temps final_memory K R C D EXEC'; eapply POINT; eassumption)
      ltac:(rewrite PTree.gso by congruence; rewrite (FRAME row ltac:(cbn; auto)); exact ROW)
      ltac:(rewrite PTree.gso by congruence; exact COLUMN) (PTree.gss _ _ _)
      ltac:(rewrite PTree.gso by congruence; rewrite (FRAME depth_bound ltac:(cbn; auto)); exact DBOUND) INNER)
      as [ITER EXIT']; split; [exact ITER|].
    rewrite EXIT'; unfold assignments; cbn [memory_settle_controls]; rewrite PTree.set2; reflexivity.
  - lia.
  - unfold signed_range; change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia.
  - lia.
  - exact ZERO.
  - exact CBOUND.
  - apply temp_agree_refl.
  - exact RUN.
Qed.
Print Assumptions memory_triple_middle_decode.

Theorem memory_triple_source_decode fe ge locals row row_bound column column_bound depth depth_bound body middle_body outer_body
  (point : Z -> Z -> Z -> mem -> mem -> Prop) rows columns depths temps memory after final :
  row <> column -> row <> depth -> row <> row_bound -> row <> column_bound -> row <> depth_bound ->
  column <> depth -> column <> column_bound -> column <> depth_bound -> column <> row_bound ->
  depth <> depth_bound -> depth <> column_bound -> depth <> row_bound ->
  normal_statement body = true -> quiet_statement body = true -> writes_only [] body ->
  signed_range (Z.of_nat rows) -> signed_range (Z.of_nat columns) -> signed_range (Z.of_nat depths) ->
  rows <> O -> columns <> O ->
  flatten_region middle_body = [rectangle_reset depth;frontend_counted_loop depth depth_bound body] ->
  flatten_region outer_body = [rectangle_reset column;frontend_counted_loop column column_bound middle_body] ->
  (forall i j k le before next target, 0 <= i < Z.of_nat rows -> 0 <= j < Z.of_nat columns -> 0 <= k < Z.of_nat depths ->
    le ! row = Some (Vint (Int.repr i)) -> le ! column = Some (Vint (Int.repr j)) -> le ! depth = Some (Vint (Int.repr k)) ->
    exec_stmt fe ge locals le before body E0 next target Out_normal -> point i j k before target /\ next = le) ->
  temps ! row = Some (Vint Int.zero) -> temps ! row_bound = Some (Vint (Int.repr (Z.of_nat rows))) ->
  temps ! column_bound = Some (Vint (Int.repr (Z.of_nat columns))) ->
  temps ! depth_bound = Some (Vint (Int.repr (Z.of_nat depths))) ->
  exec_stmt fe ge locals temps memory (frontend_counted_loop row row_bound outer_body) E0 after final Out_normal ->
  counted_iterations (fun i => counted_iterations (fun j => counted_iterations (point i j) depths 0) columns 0) rows 0 memory final /\
  after = PTree.set row (Vint (Int.repr (Z.of_nat rows)))
    (PTree.set column (Vint (Int.repr (Z.of_nat columns)))
      (PTree.set depth (Vint (Int.repr (Z.of_nat depths))) temps)).
Proof.
  intros RC RD RN RCB RDB CD CC CDB CN DD DC DN NORMAL QUIET WRITES RRANGE CRANGE DRANGE RPOS CPOS
    MIDDLE OUTER POINT ZERO BOUND CBOUND DBOUND RUN.
  set (assignments := [(column,Vint (Int.repr (Z.of_nat columns)));(depth,Vint (Int.repr (Z.of_nat depths)))]).
  assert (EXIT : PTree.set row (Vint (Int.repr (Z.of_nat rows)))
    (PTree.set column (Vint (Int.repr (Z.of_nat columns)))
      (PTree.set depth (Vint (Int.repr (Z.of_nat depths))) temps)) =
    settled_exit (memory_settle_controls assignments) row temps rows (Z.of_nat rows)).
  { destruct rows; [contradiction|reflexivity]. }
  rewrite EXIT.
  assert (MQUIET : quiet_statement middle_body = true).
  { eapply memory_reset_child_quiet; [exact MIDDLE|apply memory_frontend_loop_quiet; exact QUIET]. }
  assert (OWRITES : writes_only [column;depth] outer_body).
  { eapply memory_reset_child_writes; [exact OUTER|cbn; auto|].
    apply memory_frontend_loop_writes; [cbn; auto|].
    eapply memory_reset_child_writes; [exact MIDDLE|cbn; auto|].
    apply memory_frontend_loop_writes; [cbn; auto|].
    eapply writes_only_weaken with (small := []); [cbn; tauto|exact WRITES]. }
  assert (ONORMAL : normal_statement outer_body = true).
  { apply flatten_normal_certificate; rewrite OUTER; constructor; [reflexivity|].
    constructor; [change (quiet_statement (frontend_counted_loop column column_bound middle_body) = true);
      apply memory_frontend_loop_quiet; exact MQUIET|constructor]. }
  eapply frontend_settled_decode with (written := [column;depth]) (settle := memory_settle_controls assignments)
    (body := outer_body) (floor := 0) (stable := [column_bound;depth_bound]) (base := temps).
  - intros le key FRESH; apply memory_settle_controls_frame; exact FRESH.
  - intro le; apply memory_settle_controls_idempotent.
  - intros le value; apply memory_settle_controls_commute; unfold assignments; cbn; intuition congruence.
  - exact RN.
  - split; cbn; intuition congruence.
  - cbn; intuition congruence.
  - intros identifier MEMBER; cbn in *; intuition congruence.
  - exact ONORMAL.
  - exact OWRITES.
  - exact RRANGE.
  - intros i le before next target I ROW BOUND' FRAME EXEC.
    pose proof (@memory_reset_child_decode fe ge locals outer_body column
      (frontend_counted_loop column column_bound middle_body) le before next target OUTER EXEC) as MIDDLE_RUN.
    destruct (@memory_triple_middle_decode fe ge locals row column column_bound depth depth_bound body middle_body point
      columns depths i (PTree.set column (Vint Int.zero) le) before next target
      ltac:(congruence) ltac:(congruence) DD DC ltac:(congruence) CC CDB NORMAL QUIET WRITES CRANGE DRANGE CPOS MIDDLE
      ltac:(intros j k current initial final_temps final_memory J K R C D EXEC'; eapply POINT; eassumption)
      ltac:(rewrite PTree.gso by congruence; exact ROW) (PTree.gss _ _ _)
      ltac:(rewrite PTree.gso by congruence; rewrite (FRAME column_bound ltac:(cbn; auto)); exact CBOUND)
      ltac:(rewrite PTree.gso by congruence; rewrite (FRAME depth_bound ltac:(cbn; auto)); exact DBOUND) MIDDLE_RUN)
      as [ITER EXIT']; split; [exact ITER|].
    rewrite EXIT'; unfold assignments; cbn [memory_settle_controls].
    apply PTree.extensionality; intro key; rewrite !PTree.gsspec.
    destruct (peq key column),(peq key depth); subst; intuition congruence.
  - lia.
  - unfold signed_range; change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia.
  - lia.
  - exact ZERO.
  - exact BOUND.
  - apply temp_agree_refl.
  - exact RUN.
Qed.
Print Assumptions memory_triple_source_decode.
