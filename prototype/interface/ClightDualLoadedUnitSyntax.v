From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightRedundantSet ClightNoWrap
  ClightPureExpr ClightFiniteRegion ClightStraightLine ClightCountedLoop ClightCountedProtocol
  ClightFrontendRegion ClightLoopExecution ClightLoopSyntax ClightRegionProgress ClightTempFrame.
From GuardInterface Require Import ClightStrictLoopProgress ClightStrictIteration
  ClightStableLoopCondition ClightLoadedBoundSyntax ClightQuietDeterminacy.
Import ListNotations.
Set Implicit Arguments.

(** Two changing memory-bound dimensions. The selected special case eliminates
    a single-iteration nest; the source fallback retains every actual load. *)
Definition dual_unit_store out := Sassign (signed_load out) (Econst_int (Int.repr 2) type_int32s).
Definition dual_unit_reset column := Sset column (Econst_int Int.zero type_int32s).
Definition dual_unit_source row rows outer := loaded_bound_loop row rows outer.
Definition dual_unit_candidate row column out :=
  Ssequence (dual_unit_store out)
    (Ssequence (Sset column (Econst_int Int.one type_int32s)) (Sset row (Econst_int Int.one type_int32s))).

Lemma tail_execution_app_split fe ge locals first second le memory after final :
  tail_execution fe ge locals (first ++ second) le memory after final ->
  exists middle mem, tail_execution fe ge locals first le memory middle mem /\
    tail_execution fe ge locals second middle mem after final.
Proof.
  revert le memory; induction first as [|atom first IH]; intros le memory RUN; cbn in RUN.
  - exists le, memory; split; [constructor|exact RUN].
  - inversion RUN; subst; match goal with TAIL : tail_execution _ _ _ (first ++ second) _ _ _ _ |- _ =>
      destruct (IH _ _ TAIL) as [middle [mem [LEFT RIGHT]]] end.
    exists middle, mem; split; [econstructor; eassumption|exact RIGHT].
Qed.
Lemma flatten_region_encode fe ge locals source le memory after final :
  tail_execution fe ge locals (flatten_region source) le memory after final ->
  exec_stmt fe ge locals le memory source E0 after final Out_normal.
Proof.
  revert le memory after final; induction source; intros le memory after final RUN; cbn [flatten_region] in RUN.
  all: try solve [inversion RUN; subst;
    match goal with LAST : tail_execution _ _ _ [] _ _ _ _ |- _ => inversion LAST; subst end; assumption].
  - inversion RUN; subst; constructor.
  - destruct (@tail_execution_app_split fe ge locals (flatten_region source1) (flatten_region source2)
      le memory after final RUN) as [middle [mem [LEFT RIGHT]]].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := middle) (m1 := mem).
    + exact (IHsource1 _ _ _ _ LEFT).
    + exact (IHsource2 _ _ _ _ RIGHT).
Qed.
Lemma flattened_singleton_encode fe ge locals source atom le memory after final :
  flatten_region source = [atom] -> exec_stmt fe ge locals le memory atom E0 after final Out_normal ->
  exec_stmt fe ge locals le memory source E0 after final Out_normal.
Proof. intros FLAT RUN; apply flatten_region_encode; rewrite FLAT; econstructor; [exact RUN|constructor]. Qed.
Lemma flattened_pair_encode fe ge locals source first second le memory middle mem after final :
  flatten_region source = [first;second] ->
  exec_stmt fe ge locals le memory first E0 middle mem Out_normal ->
  exec_stmt fe ge locals middle mem second E0 after final Out_normal ->
  exec_stmt fe ge locals le memory source E0 after final Out_normal.
Proof.
  intros FLAT LEFT RIGHT; apply flatten_region_encode; rewrite FLAT;
    econstructor; [exact LEFT|econstructor; [exact RIGHT|constructor]].
Qed.

Lemma strict_zero_trip_encode fe ge locals le memory iterator condition body :
  expression_test condition (Entry ge locals le memory) false ->
  exec_stmt fe ge locals le memory (strict_frontend_loop iterator condition body) E0 le memory Out_normal.
Proof.
  intros [value [EVAL BOOL]]; eapply exec_Sloop_stop1 with (out' := Out_break).
  - eapply exec_Sseq_2 with (out := Out_break); [|discriminate].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [constructor|].
    eapply exec_Sifthenelse; [exact EVAL|exact BOOL|constructor].
  - constructor.
Qed.
Lemma strict_iteration_encode fe ge locals le memory iterator condition body body_temps body_memory after final :
  expression_test condition (Entry ge locals le memory) true -> strict_counter_active iterator body_temps ->
  exec_stmt fe ge locals le memory body E0 body_temps body_memory Out_normal ->
  exec_stmt fe ge locals (increment_temps iterator body_temps) body_memory
    (strict_frontend_loop iterator condition body) E0 after final Out_normal ->
  exec_stmt fe ge locals le memory (strict_frontend_loop iterator condition body) E0 after final Out_normal.
Proof.
  intros [value [EVAL BOOL]] ACTIVE BODY REST.
  eapply exec_Sloop_loop with (t1 := E0) (t2 := E0) (t3 := E0) (out1 := Out_normal).
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [|exact BODY].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [constructor|].
    eapply exec_Sifthenelse; [exact EVAL|exact BOOL|constructor].
  - constructor.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [constructor|apply strict_increment_normal; exact ACTIVE].
  - exact REST.
Qed.

Lemma dual_unit_store_encode fe ge locals le memory out b ofs final :
  le ! out = Some (Vptr b ofs) -> Mem.storev Mint32 memory (Vptr b ofs) (Vint (Int.repr 2)) = Some final ->
  exec_stmt fe ge locals le memory (dual_unit_store out) E0 le final Out_normal.
Proof.
  intros P STORE; eapply exec_Sassign with (v := Vint (Int.repr 2)) (v2 := Vint (Int.repr 2)) (bf := Full).
  - apply eval_Ederef, eval_Etempvar; exact P.
  - constructor.
  - reflexivity.
  - apply assign_loc_value with (chunk := Mint32); [reflexivity|exact STORE].
Qed.
Lemma dual_unit_store_decode fe ge locals le memory out after final :
  exec_stmt fe ge locals le memory (dual_unit_store out) E0 after final Out_normal ->
  exists b ofs, le ! out = Some (Vptr b ofs) /\ after = le /\
    Mem.storev Mint32 memory (Vptr b ofs) (Vint (Int.repr 2)) = Some final.
Proof.
  intro RUN; inversion RUN; subst.
  match goal with LV : eval_lvalue _ _ _ _ (signed_load out) _ _ _ |- _ => inversion LV; subst end.
  match goal with P : eval_expr _ _ _ _ (signed_pointer_temp out) _ |- _ => apply scalar_temp_inv in P end.
  match goal with V : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ => apply scalar_const_inv in V; subst end.
  match goal with CAST : sem_cast _ _ _ _ = Some _ |- _ => inversion CAST; subst end.
  match goal with STORE : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion STORE; subst; try discriminate end.
  match goal with MODE : access_mode _ = By_value _ |- _ => inversion MODE; subst end.
  do 2 eexists; repeat split; eauto.
Qed.
Lemma dual_unit_body_quiet out body : flatten_region body = [dual_unit_store out] -> quiet_statement body = true.
Proof. intro FLAT; apply flatten_quiet_certificate; rewrite FLAT; constructor; [reflexivity|constructor]. Qed.
Lemma dual_unit_outer_quiet out column columns body outer :
  flatten_region body = [dual_unit_store out] ->
  flatten_region outer = [dual_unit_reset column; loaded_bound_loop column columns body] -> quiet_statement outer = true.
Proof.
  intros BODY OUTER; apply flatten_quiet_certificate; rewrite OUTER; constructor; [reflexivity|constructor; [|constructor]].
  cbn [loaded_bound_loop strict_frontend_loop quiet_statement counter_increment]; rewrite (@dual_unit_body_quiet out body BODY); reflexivity.
Qed.
Lemma dual_unit_outer_normal out column columns body outer :
  flatten_region body = [dual_unit_store out] ->
  flatten_region outer = [dual_unit_reset column; loaded_bound_loop column columns body] -> normal_statement outer = true.
Proof.
  intros BODY OUTER; apply flatten_normal_certificate; rewrite OUTER; constructor; [reflexivity|constructor; [|constructor]].
  cbn [loaded_bound_loop strict_frontend_loop normal_statement quiet_statement counter_increment];
    rewrite (@dual_unit_body_quiet out body BODY); reflexivity.
Qed.
Lemma dual_unit_source_quiet row rows out column columns body outer :
  flatten_region body = [dual_unit_store out] ->
  flatten_region outer = [dual_unit_reset column; loaded_bound_loop column columns body] ->
  quiet_statement (dual_unit_source row rows outer) = true.
Proof.
  intros BODY OUTER; cbn [dual_unit_source loaded_bound_loop strict_frontend_loop quiet_statement counter_increment];
    rewrite (@dual_unit_outer_quiet out column columns body outer BODY OUTER); reflexivity.
Qed.
Lemma loaded_source_head fe ge locals iterator bound body le memory after final :
  exec_stmt fe ge locals le memory (loaded_bound_loop iterator bound body) E0 after final Out_normal ->
  exists flag, expression_test (loaded_bound_test iterator bound) (Entry ge locals le memory) flag.
Proof.
  intro SOURCE; inversion SOURCE; subst.
  all: match goal with HEADER : exec_stmt _ _ _ _ _ (Ssequence (Ssequence Sskip _) _) _ _ _ _ |- _ =>
    destruct (strict_header_execution HEADER) as [flag [TEST _]]; exists flag; exact TEST end.
Qed.

Print Assumptions flatten_region_encode.
Print Assumptions strict_zero_trip_encode.
Print Assumptions strict_iteration_encode.
Print Assumptions dual_unit_store_decode.
Print Assumptions dual_unit_source_quiet.
