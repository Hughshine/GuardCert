From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib.
From Guard Require Import ClightCountedLoop.
From GuardMemory Require Import GuardMemoryIntervalBox GuardMemoryAffineSourceValuation
  GuardMemoryAffineSourceExpressions.
From GuardAffineNest Require Import AffineNestSyntax AffineNestProfile AffineNestValuation AffineNestMathDomain.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma affine_ranges_append first_bounds first_values second_bounds second_values :
  interval_ranges first_bounds first_values -> interval_ranges second_bounds second_values ->
  interval_ranges (first_bounds++second_bounds) (first_values++second_values).
Proof. intros FIRST SECOND; induction FIRST; cbn; [exact SECOND|constructor; assumption]. Qed.
Lemma affine_ranges_reverse bounds values : interval_ranges bounds values ->
  interval_ranges (rev bounds) (rev values).
Proof.
  intro RANGES; induction RANGES; cbn; [constructor|].
  apply affine_ranges_append; [exact IHRANGES|constructor; [exact H|constructor]].
Qed.

Definition affine_profile_start nest (ranges : list(Z*Z)) lower := match nest,ranges with
  | AffineSourceLeaf _,_ => True
  | AffineSourceAxis _ _ _ _ _,(floor,_)::_ => floor<=lower
  | _,_ => False end.
Lemma affine_child_profile_start_sound child ranges :
  affine_child_profile_start_check child ranges=true -> affine_profile_start child ranges 0.
Proof.
  destruct child; [exact(fun _=>I)|]; destruct ranges as [|[floor cap] rest]; [discriminate|].
  cbn [affine_child_profile_start_check affine_profile_start]; apply Z.leb_le.
Qed.

Theorem checked_affine_profile_domain nest : forall prefix parameters prefix_ranges parameter_ranges
  axis_ranges leaf_bounds leaf_layout valuation lower,
  check_affine_math_profile nest prefix parameters prefix_ranges parameter_ranges axis_ranges leaf_bounds leaf_layout=true ->
  NoDup(affine_nest_iterators nest) ->
  (forall iterator, In iterator(affine_nest_iterators nest) -> ~In iterator(prefix++parameters)) ->
  interval_ranges prefix_ranges(map valuation prefix) ->
  interval_ranges parameter_ranges(map valuation parameters) ->
  signed_range lower -> affine_profile_start nest axis_ranges lower ->
  affine_math_domain leaf_bounds leaf_layout nest valuation lower.
Proof.
  induction nest as [source|iterator bound expression body child IH];
    intros prefix parameters prefix_ranges parameter_ranges axis_ranges leaf_bounds leaf_layout valuation lower
      CHECK UNIQUE FRESH PREFIX PARAMETERS SIGNED START.
  - cbn [check_affine_math_profile] in CHECK; destruct axis_ranges; [|discriminate].
    destruct(list_eq_dec peq leaf_layout (prefix++parameters)) as [LAYOUT|]; [|discriminate].
    destruct(list_eq_dec affine_range_eq_dec leaf_bounds(prefix_ranges++parameter_ranges)) as [BOUNDS|]; [|discriminate].
    subst leaf_layout leaf_bounds; cbn [affine_math_domain]; rewrite map_app.
    apply affine_ranges_append; assumption.
  - cbn [check_affine_math_profile] in CHECK; destruct axis_ranges as [|[floor cap] remaining]; [discriminate|].
    rewrite !andb_true_iff in CHECK.
    destruct CHECK as [[[[[FLOOR CAP] NONEMPTY] BOUND] CHILD_START] CHILD_CHECK].
    assert (CURRENT_FRESH:~In iterator(prefix++parameters)) by (apply FRESH; cbn; auto).
    assert (PREFIX_FRESH:~In iterator prefix).
    { intro MEMBER; apply CURRENT_FRESH,in_or_app; auto. }
    assert (PARAMETERS_FRESH:~In iterator parameters).
    { intro MEMBER; apply CURRENT_FRESH,in_or_app; auto. }
    assert (BOX:interval_ranges (rev prefix_ranges++parameter_ranges) (map valuation(rev prefix++parameters))).
    { rewrite map_app,map_rev; apply affine_ranges_append; [apply affine_ranges_reverse; exact PREFIX|exact PARAMETERS]. }
    destruct (@affine_checked_math_bound (rev prefix++parameters)
      (map affine_profile_interval(rev prefix_ranges++parameter_ranges)) expression cap valuation BOUND
      (@affine_profile_ranges_within _ _ BOX)) as [UPPER WITHIN].
    cbn [affine_math_domain]; split; [exact SIGNED|split; [exact UPPER|]].
    intros value RANGE.
    inversion UNIQUE as [|first rest ITERATOR_FRESH CHILD_UNIQUE]; subst.
    apply IH with (prefix:=prefix++[iterator]) (parameters:=parameters)
      (prefix_ranges:=prefix_ranges++[(floor,cap)]) (parameter_ranges:=parameter_ranges)
      (axis_ranges:=remaining).
    + exact CHILD_CHECK.
    + exact CHILD_UNIQUE.
    + intros identifier MEMBER BAD; repeat rewrite in_app_iff in BAD; cbn in BAD.
      assert (OLD:~In identifier(prefix++parameters)).
      { apply FRESH; cbn; auto. }
      destruct BAD as [[BAD|[SAME|FALSE]]|BAD].
      * apply OLD,in_or_app; auto.
      * subst identifier; exact(ITERATOR_FRESH MEMBER).
      * contradiction.
      * apply OLD,in_or_app; auto.
    + rewrite map_app,affine_valuation_update_map by exact PREFIX_FRESH.
      cbn [map]; unfold memory_source_set_valuation at 1.
      destruct(peq iterator iterator); [|contradiction].
      apply affine_ranges_append; [exact PREFIX|].
      constructor; [cbn [fst snd]; cbn [affine_profile_start] in START; lia|constructor].
    + rewrite affine_valuation_update_map by exact PARAMETERS_FRESH; exact PARAMETERS.
    + unfold signed_range; change(-2147483648<=0<=2147483647); lia.
    + apply affine_child_profile_start_sound; exact CHILD_START.
Qed.
Print Assumptions checked_affine_profile_domain.
