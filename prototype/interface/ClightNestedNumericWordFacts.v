From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightTempFrame ClightNoWrap ClightPureExpr ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryIntervalGuard GuardMemoryWindowParameterGuard GuardMemoryAffineSourceExpressions.
From GuardAffineNest Require Import AffineNestExit AffineNestGuardPackage AffineNestPackageGuard AffineNestDomainGuard
  AffineNestProbe AffineNestNumericGuard AffineNestGuardFactTransport AffineNestMathDomain.
From GuardInterface Require Import ClightNestedConstantSite ClightNestedConstantSiteFacts
  ClightNestedConstantSitePrepare ClightNestedConstantSiteNumeric ClightNestedConstantNumericGuard.
Import ListNotations.
Set Implicit Arguments.

(** A computable, memory-independent view of the existing numeric condition.
    This certifies sufficient facts; it does not license captures or replace
    their execution/frame receipts. *)
Definition numeric_interval_temps identifier lower upper temps :=
  negb(Int.lt(temp_word identifier temps)(Int.repr lower)) &&
  negb(Int.lt(Int.repr(upper-1))(temp_word identifier temps)).
Fixpoint numeric_parameters_temps ranges identifiers temps :=
  match ranges,identifiers with
  | [],[] => true
  | (lower,upper)::rest,identifier::tail =>
      numeric_interval_temps identifier lower upper temps && numeric_parameters_temps rest tail temps
  | _,_ => false end.
Definition ncs_numeric_temps_flag parameters proposal shape temps :=
  if Int.lt Int.zero(temp_word(ncs_root_cache shape)temps) then
    if Int.lt Int.zero(temp_word(ncs_child_cache shape)temps) then
      affine_first_path_flag(affine_proposal_nest proposal) temps &&
      (numeric_parameters_temps(affine_proposed_parameter_ranges proposal) parameters temps &&
       numeric_interval_temps(affine_proposed_iterator proposal)(affine_proposed_floor proposal)
         (affine_proposed_cap proposal) temps)
    else false
  else false.

Lemma numeric_parameters_temps_exact ranges : forall identifiers ge locals temps memory,
  numeric_parameters_temps ranges identifiers temps =
    window_parameters_accept ranges identifiers(Entry ge locals temps memory).
Proof.
  induction ranges as [|[lower upper] rest IH]; intros [|identifier tail] ge locals temps memory;
    cbn [numeric_parameters_temps window_parameters_accept]; try reflexivity.
  rewrite(IH tail ge locals temps memory); reflexivity.
Qed.

Theorem ncs_numeric_temps_flag_exact parameters proposal shape ge locals temps memory :
  ncs_numeric_temps_flag parameters proposal shape temps =
    ncs_numeric_flag parameters proposal shape(Entry ge locals temps memory).
Proof.
  unfold ncs_numeric_temps_flag,ncs_numeric_flag,nested_constant_numeric_flag,
    affine_package_guard_flag,affine_domain_guard_flag,affine_numeric_guard_flag,register_positive.
  cbn [entry_temps]; rewrite(@numeric_parameters_temps_exact(affine_proposed_parameter_ranges proposal)
    parameters ge locals temps memory); reflexivity.
Qed.

Definition ncs_numeric_word_temps shape word :=
  PTree.set(ncs_child_cache shape)(Vint(Int.add word(ncs_child_delta shape)))
    (PTree.set(ncs_root_cache shape)(Vint(Int.add word(ncs_delta shape)))
      (PTree.set(ncs_row shape)(Vint Int.zero)(PTree.empty val))).
Definition ncs_numeric_word_check parameters proposal shape word :=
  forallb(fun identifier=>Pos.eqb identifier(ncs_root_cache shape) ||
    Pos.eqb identifier(ncs_child_cache shape)) parameters &&
  ncs_numeric_temps_flag parameters proposal shape(ncs_numeric_word_temps shape word).

Section FACTS.
Variables source : statement.
Variables parameters live : list ident.
Variable proposal : affine_guard_proposal.
Variable shape : nested_constant_shape.
Variable site : nested_constant_site source parameters live proposal shape.

Theorem ncs_numeric_word_sufficient ge locals temps memory word :
  ncs_numeric_word_check parameters proposal shape word=true ->
  temps!(ncs_row shape)=Some(Vint Int.zero) ->
  temps!(ncs_root_cache shape)=Some(Vint(Int.add word(ncs_delta shape))) ->
  temps!(ncs_child_cache shape)=Some(Vint(Int.add word(ncs_child_delta shape))) ->
  ncs_numeric_flag parameters proposal shape(Entry ge locals temps memory)=true.
Proof.
  intros CHECK ROW ROOT CHILD; unfold ncs_numeric_word_check in CHECK.
  apply andb_true_iff in CHECK as [COVER FLAG].
  assert(ROOT_ROW : ncs_root_cache shape<>ncs_row shape).
  { intro SAME; apply(ncs_site_parameters_coordinates site (ncs_cache_parameters site (or_introl eq_refl))).
    unfold ncs_coordinates; left; symmetry; exact SAME. }
  assert(CHILD_ROW : ncs_child_cache shape<>ncs_row shape).
  { intro SAME; apply(ncs_site_row_child_distinct site); symmetry; exact SAME. }
  assert(ROOT_CHILD : ncs_root_cache shape<>ncs_child_cache shape) by exact(ncs_site_caches_distinct site).
  assert(KNOWN_ROOT : (ncs_numeric_word_temps shape word)!(ncs_root_cache shape)=
    Some(Vint(Int.add word(ncs_delta shape)))).
  { unfold ncs_numeric_word_temps; rewrite PTree.gso by exact ROOT_CHILD; apply PTree.gss. }
  assert(KNOWN_CHILD : (ncs_numeric_word_temps shape word)!(ncs_child_cache shape)=
    Some(Vint(Int.add word(ncs_child_delta shape)))) by(apply PTree.gss).
  assert(KNOWN_ROW : (ncs_numeric_word_temps shape word)!(ncs_row shape)=Some(Vint Int.zero)).
  { unfold ncs_numeric_word_temps; rewrite !PTree.gso by congruence; apply PTree.gss. }
  assert(FRAME : temp_agree(parameters++[ncs_row shape;ncs_root_cache shape])
    (ncs_numeric_word_temps shape word) temps).
  { intros identifier MEMBER; apply in_app_iff in MEMBER as [PARAMETER|CONTROL].
    - apply forallb_forall with(x:=identifier) in COVER; [|exact PARAMETER].
      apply orb_true_iff in COVER as [R|C]; apply Pos.eqb_eq in R || apply Pos.eqb_eq in C;
        subst identifier; congruence.
    - cbn [List.In] in CONTROL; destruct CONTROL as [R|[C|[]]]; subst identifier; congruence. }
  rewrite(@ncs_numeric_flag_frame _ _ _ _ _ site ge locals memory(ncs_numeric_word_temps shape word) temps FRAME).
  rewrite <-(@ncs_numeric_temps_flag_exact parameters proposal shape ge locals(ncs_numeric_word_temps shape word)memory); exact FLAG.
Qed.

Theorem ncs_numeric_word_math_domain (ge:genv) (locals:env) temps (memory:mem) word :
  ncs_numeric_word_check parameters proposal shape word=true ->
  temps!(ncs_row shape)=Some(Vint Int.zero) ->
  temps!(ncs_root_cache shape)=Some(Vint(Int.add word(ncs_delta shape))) ->
  temps!(ncs_child_cache shape)=Some(Vint(Int.add word(ncs_child_delta shape))) ->
  affine_math_domain(affine_proposed_leaf_bounds proposal)(affine_proposal_layout proposal parameters)
    (affine_proposal_nest proposal)(affine_word_valuation temps) 0.
Proof.
  intros CHECK ROW ROOT CHILD; apply(ncs_numeric_flag_domain site(Entry ge locals temps memory)ROW).
  exact(@ncs_numeric_word_sufficient ge locals temps memory word CHECK ROW ROOT CHILD).
Qed.
End FACTS.

Print Assumptions numeric_parameters_temps_exact.
Print Assumptions ncs_numeric_temps_flag_exact.
Print Assumptions ncs_numeric_word_sufficient.
Print Assumptions ncs_numeric_word_math_domain.
