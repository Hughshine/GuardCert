From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightTempFrame ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRectangles GuardMemoryNaryAffineAccess GuardMemoryAffineSourceExpressions
  GuardMemoryBooleanScan GuardMemoryFootprintCapabilities GuardMemoryWindowCells.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestValuation AffineNestMathDomain
  AffineNestScanModel AffineNestScanNamespace AffineNestScanPair AffineNestScanAccesses AffineNestScanSeparation AffineNestScanSequence.
Import ListNotations.
Set Implicit Arguments.

Definition affine_scan_pairs (accesses:list memory_nary_access) :=
  flat_map(fun first=>map(fun second=>(first,second)) accesses) accesses.
Definition affine_scan_access_pair_code nest left right flag lower pair :=
  let '(first,second):=pair in
  if Pos.eqb(memory_nary_access_array first)(memory_nary_access_array second) then Sskip else
    affine_scan_pair_statement nest left right flag lower(memory_nary_access_array first)(memory_nary_access_array second)
      (memory_nary_access_expression first)(memory_nary_access_expression second).
Definition affine_scan_all_code nest left right flag lower accesses :=
  affine_scan_sequence(affine_scan_access_pair_code nest left right flag lower)(affine_scan_pairs accesses).

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

Lemma affine_scan_all_result nest valuation lower locations accesses :
  affine_scan_sequence_result(fun pair=>affine_scan_access_pair_result nest valuation lower locations(fst pair)(snd pair))
    (affine_scan_pairs accesses)=affine_scan_separation_result nest valuation lower locations accesses.
Proof. rewrite affine_scan_sequence_forall; unfold affine_scan_pairs,affine_scan_separation_result; apply affine_scan_pairs_forall. Qed.
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
  intros [first second] MEMBER temps good CURRENT GOOD; apply affine_scan_pairs_member in MEMBER as [FIRST SECOND].
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
