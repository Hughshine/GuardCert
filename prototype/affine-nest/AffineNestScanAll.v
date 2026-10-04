From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightTempFrame ClightCountedLoop CompCertMemoryActions ClightRectangularStore.
From GuardMemory Require Import GuardMemoryFiniteFootprint GuardMemoryFiniteAliasCondition GuardMemoryRuntime GuardMemoryRectangles GuardMemoryNaryAffineAccess GuardMemoryAffineSourceExpressions
  GuardMemoryBooleanScan GuardMemoryFootprintCapabilities GuardMemoryWindowCells.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestValuation AffineNestMathDomain
  AffineNestScanModel AffineNestScanNamespace AffineNestScanPair AffineNestScanAccesses AffineNestScanSeparation AffineNestScanSequence.
Import ListNotations.
Set Implicit Arguments.

Definition memory_scan_expression_eq_dec (first second:memory_source_affine) : {first=second}+{first<>second}.
Proof. decide equality; try apply Pos.eq_dec; apply Z.eq_dec. Defined.
Definition memory_scan_shape_eq_dec (first second:rectangle_shape) : {first=second}+{first<>second}.
Proof. decide equality; apply Z.eq_dec. Defined.
Definition memory_scan_access_eq_dec (first second:memory_nary_access) : {first=second}+{first<>second}.
Proof.
  decide equality; try apply memory_scan_expression_eq_dec; try apply memory_scan_shape_eq_dec;
    try apply Pos.eq_dec; decide equality; try apply Z.eq_dec; apply list_eq_dec; apply Z.eq_dec.
Defined.
(* Deduplicate complete descriptors, so all source-membership and permission
   evidence can be reused without proving an address-expression equivalence. *)
Definition affine_unique_scan_accesses accesses := nodup memory_scan_access_eq_dec accesses.
Lemma affine_unique_scan_accesses_member first accesses :
  In first (affine_unique_scan_accesses accesses) <-> In first accesses.
Proof. apply nodup_In. Qed.

Definition affine_scan_pairs (accesses:list memory_nary_access) :=
  flat_map(fun first=>map(fun second=>(first,second)) accesses) accesses.
(* Address inequality is symmetric. Keep one direction for different pointer
   identifiers; the result proof below preserves the full separation predicate. *)
Definition affine_ordered_scan_pairs (accesses:list memory_nary_access) :=
  filter(fun pair=>Z.ltb (Z.pos(memory_nary_access_array(fst pair)))
    (Z.pos(memory_nary_access_array(snd pair))))(affine_scan_pairs (affine_unique_scan_accesses accesses)).

Definition affine_scan_access_pair_code nest left right flag lower pair :=
  let '(first,second):=pair in
  if Pos.eqb(memory_nary_access_array first)(memory_nary_access_array second) then Sskip else
    affine_scan_pair_statement nest left right flag lower(memory_nary_access_array first)(memory_nary_access_array second)
      (memory_nary_access_expression first)(memory_nary_access_expression second).
Definition affine_scan_all_code nest left right flag lower accesses :=
  affine_scan_sequence(affine_scan_access_pair_code nest left right flag lower)(affine_ordered_scan_pairs accesses).

Lemma affine_scan_pairs_member accesses first second :
  In(first,second)(affine_scan_pairs accesses) <-> In first accesses /\ In second accesses.
Proof.
  unfold affine_scan_pairs; rewrite in_flat_map; split.
  - intros [left [LEFT MEMBER]]; apply in_map_iff in MEMBER as [right [SAME RIGHT]]; inversion SAME; subst; auto.
  - intros [FIRST SECOND]; exists first; split; [exact FIRST|apply in_map; exact SECOND].
Qed.
Lemma affine_scan_pairs_forall {A:Type} (test:A->A->bool) first second :
  forallb(fun pair=>test(fst pair)(snd pair))(flat_map(fun left=>map(fun right=>(left,right)) second) first)=
    forallb(fun left=>forallb(test left) second) first.
Proof.
  assert(MAPPED:forall left, forallb(fun pair=>test(fst pair)(snd pair))(map(fun right=>(left,right)) second)=forallb(test left) second).
  { intro left; induction second; cbn; [reflexivity|rewrite IHsecond; reflexivity]. }
  induction first; cbn; [reflexivity|rewrite forallb_app,MAPPED,IHfirst; reflexivity].
Qed.

Lemma memory_cell_pair_address_check_symmetric locations first second :
  memory_cell_pair_address_check locations first second =
  memory_cell_pair_address_check locations second first.
Proof.
  unfold memory_cell_pair_address_check.
  destruct(memory_cell_identity_dec first second) as [SAME|DIFFERENT].
  - subst second; destruct(memory_cell_identity_dec first first); congruence.
  - destruct(memory_cell_identity_dec second first); [congruence|].
    destruct(locations first), (locations second); try reflexivity.
    rewrite Pos.eqb_sym,Z.eqb_sym; reflexivity.
Qed.
Lemma affine_scan_pair_result_symmetric nest valuation lower locations first second a b :
  affine_scan_pair_result nest valuation lower locations first second a b =
  affine_scan_pair_result nest valuation lower locations second first b a.
Proof.
  apply Bool.eq_true_iff_eq; unfold affine_scan_pair_result;
    rewrite !affine_scan_result_points; split; intros CHECK outer OUTER;
    apply affine_scan_result_points; intros inner INNER;
    specialize(CHECK inner INNER);
    pose proof(proj1(@affine_scan_result_points nest valuation lower _) CHECK outer OUTER) as PAIR;
    rewrite memory_cell_pair_address_check_symmetric; exact PAIR.
Qed.
Lemma affine_scan_access_pair_result_symmetric nest valuation lower locations first second :
  affine_scan_access_pair_result nest valuation lower locations first second =
  affine_scan_access_pair_result nest valuation lower locations second first.
Proof.
  unfold affine_scan_access_pair_result.
  rewrite (Pos.eqb_sym (memory_nary_access_array second)(memory_nary_access_array first)).
  destruct(Pos.eqb (memory_nary_access_array first)(memory_nary_access_array second));
    [reflexivity|apply affine_scan_pair_result_symmetric].
Qed.

Lemma affine_ordered_scan_pairs_result nest valuation lower locations accesses :
  forallb(fun pair=>affine_scan_access_pair_result nest valuation lower locations(fst pair)(snd pair))
    (affine_ordered_scan_pairs accesses)=affine_scan_separation_result nest valuation lower locations accesses.
Proof.
  apply Bool.eq_true_iff_eq; unfold affine_scan_separation_result; split; intro CHECK.
  - apply forallb_forall; intros first FIRST; apply forallb_forall; intros second SECOND.
    destruct(Z.lt_trichotomy (Z.pos(memory_nary_access_array first))
      (Z.pos(memory_nary_access_array second))) as [ORDER|[SAME|REVERSE]].
    + apply forallb_forall with(x:=(first,second)) in CHECK; [exact CHECK|].
      unfold affine_ordered_scan_pairs; apply filter_In; split.
      * apply affine_scan_pairs_member; split; apply affine_unique_scan_accesses_member; assumption.
      * apply Z.ltb_lt; exact ORDER.
    + injection SAME as SAME; unfold affine_scan_access_pair_result.
      rewrite SAME,Pos.eqb_refl; reflexivity.
    + rewrite affine_scan_access_pair_result_symmetric.
      apply forallb_forall with(x:=(second,first)) in CHECK; [exact CHECK|].
      unfold affine_ordered_scan_pairs; apply filter_In; split.
      * apply affine_scan_pairs_member; split; apply affine_unique_scan_accesses_member; assumption.
      * apply Z.ltb_lt; exact REVERSE.
  - apply forallb_forall; intros [first second] MEMBER.
    unfold affine_ordered_scan_pairs in MEMBER; apply filter_In in MEMBER as [MEMBER ORDER].
    apply affine_scan_pairs_member in MEMBER as [FIRST SECOND];
    apply (proj1(@affine_unique_scan_accesses_member first accesses)) in FIRST;
    apply (proj1(@affine_unique_scan_accesses_member second accesses)) in SECOND.
    apply forallb_forall with(x:=first) in CHECK; [|exact FIRST].
    apply forallb_forall with(x:=second) in CHECK; [exact CHECK|exact SECOND].
Qed.

Lemma affine_scan_all_result nest valuation lower locations accesses :
  affine_scan_sequence_result(fun pair=>affine_scan_access_pair_result nest valuation lower locations(fst pair)(snd pair))
    (affine_ordered_scan_pairs accesses)=affine_scan_separation_result nest valuation lower locations accesses.
Proof. rewrite affine_scan_sequence_forall; apply affine_ordered_scan_pairs_result. Qed.
Print Assumptions affine_scan_all_result.

Theorem affine_scan_all_execution iterator bound expression body child parameters live left right flag
  (left_names:affine_scan_namespace(AffineSourceAxis iterator bound expression body child) parameters live left flag)
  (right_names:affine_scan_namespace(AffineSourceAxis iterator bound expression body child) parameters
    (map left(affine_nest_controls(AffineSourceAxis iterator bound expression body child))++live) right flag)
  fe ge locals original current memory valuation lower accepted bounds layout window_lower window_upper accesses :
  let nest:=AffineSourceAxis iterator bound expression body child in
  affine_nest_bound_dependencies [] parameters nest -> incl parameters live -> In iterator live ->
  signed_range window_lower -> signed_range(window_upper-1) ->
  affine_math_domain bounds layout nest valuation lower -> affine_word_view parameters valuation original ->
  original!iterator=Some(Vint(Int.repr lower)) -> temp_agree live original current ->
  current!flag=Some(memory_boolean_word accepted) ->
  (forall access, In access accesses -> In(memory_nary_access_array access) live /\
    (forall identifier, In identifier(memory_source_affine_reads(memory_nary_access_expression access)) ->
      In identifier(affine_nest_iterators nest++parameters))) ->
  (forall point, affine_scan_point nest valuation lower point ->
    Forall(memory_cell_capable(window_multi_pointer_locations original window_lower window_upper) memory)
      (map(affine_scan_access_cell point) accesses)) ->
  exists after,
    exec_stmt fe ge locals current memory
      (affine_scan_all_code nest left right flag(Etempvar iterator type_int32s) accesses) E0 after memory Out_normal /\
    temp_agree live current after /\ after!flag=Some(memory_boolean_word(accepted&&affine_scan_separation_result nest valuation lower
      (window_multi_pointer_locations original window_lower window_upper) accesses)).
Proof.
  cbn zeta; intros DEPENDENCIES PARAMETERS ROOT LOW HIGH DOMAIN WORDS ROOT_WORD FRAME FLAG ACCESS CAPABLE.
  unfold affine_scan_all_code; rewrite <-affine_scan_all_result.
  eapply affine_scan_sequence_execution with(original:=original); [|exact FRAME|exact FLAG].
  intros [first second] MEMBER temps good CURRENT GOOD; unfold affine_ordered_scan_pairs in MEMBER;
  apply filter_In in MEMBER as [MEMBER ORDER]; apply affine_scan_pairs_member in MEMBER as [FIRST SECOND];
    apply (proj1(@affine_unique_scan_accesses_member first accesses)) in FIRST;
    apply (proj1(@affine_unique_scan_accesses_member second accesses)) in SECOND.
  unfold affine_scan_access_pair_code; cbn [fst snd].
  unfold affine_scan_access_pair_result; destruct(Pos.eqb(memory_nary_access_array first)(memory_nary_access_array second)) eqn:SAME.
  - exists temps; rewrite andb_true_r; repeat split; auto using exec_Sskip,temp_agree_refl.
  - apply Pos.eqb_neq in SAME.
    eapply affine_scan_pair_execution with(left_names:=left_names)(right_names:=right_names)
      (original:=original)(valuation:=valuation)(bounds:=bounds)(layout:=layout); try eassumption.
    + exact(proj1(ACCESS first FIRST)).
    + exact(proj1(ACCESS second SECOND)).
    + exact(proj2(ACCESS first FIRST)).
    + exact(proj2(ACCESS second SECOND)).
    + intros point POINT; split.
      * pose proof(CAPABLE point POINT) as CELLS.
        apply Forall_forall with(x:=affine_scan_access_cell point first) in CELLS;
          [exact CELLS|apply in_map; exact FIRST].
      * pose proof(CAPABLE point POINT) as CELLS.
        apply Forall_forall with(x:=affine_scan_access_cell point second) in CELLS;
          [exact CELLS|apply in_map; exact SECOND].
Qed.
Print Assumptions affine_scan_all_execution.
