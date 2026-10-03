From Stdlib Require Import List Bool ZArith.
From polcert.src Require Import PolyBase.
From Guard Require Import AbstractGuard ClightCondition ClightPureExpr.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRegistryGuard GuardMemoryFootprintRestriction
  GuardMemoryFiniteFootprint GuardMemoryFiniteAliasCondition.
Import ListNotations.
Set Implicit Arguments.

Record memory_activated_cell := MemoryActivatedCell {
  activated_cell : MemCell;
  activated_test : decision_tree;
  activated_coordinates : list Z
}.
Definition memory_selected_cells active items :=
  map activated_cell (filter active items).
Definition memory_activation_exact s active item :=
  forall flag, decision_run s (activated_test item) flag <-> flag = active item.
Definition memory_activated_address_binding code locations s active item :=
  active item = true -> memory_cell_address_binding code locations s (activated_cell item).
Definition memory_activated_pair_tree code first second :=
  if memory_cell_identity_dec (activated_cell first) (activated_cell second) then Decision true else
    decision_bind (activated_test first)
      (decision_bind (activated_test second)
        (memory_cell_pair_address_tree code (activated_cell first) (activated_cell second)) (Decision true))
      (Decision true).
Definition memory_activated_pair_check locations (active : memory_activated_cell -> bool) first second :=
  if active first then
    if active second then memory_cell_pair_address_check locations (activated_cell first) (activated_cell second)
    else true
  else true.
Theorem memory_activated_pair_exact code locations s active first second :
  memory_activation_exact s active first -> memory_activation_exact s active second ->
  memory_activated_address_binding code locations s active first ->
  memory_activated_address_binding code locations s active second ->
  forall flag, decision_run s (memory_activated_pair_tree code first second) flag <->
    flag = memory_activated_pair_check locations active first second.
Proof.
  intros FIRST_TEST SECOND_TEST FIRST_ADDRESS SECOND_ADDRESS flag.
  unfold memory_activated_pair_tree,memory_activated_pair_check.
  destruct (memory_cell_identity_dec (activated_cell first) (activated_cell second)) as [SAME|DIFFERENT].
  - unfold memory_cell_pair_address_check; destruct memory_cell_identity_dec; [|congruence].
    destruct (active first),(active second); cbn;
      (split; [intro RUN; inversion RUN; reflexivity|intro EQUAL; subst; constructor]).
  - change (command_run decision_test_language
      (conditional decision_test_language (activated_test first)
        (decision_bind (activated_test second)
          (memory_cell_pair_address_tree code (activated_cell first) (activated_cell second)) (Decision true))
        (Decision true)) s flag <-> flag =
        (if active first then if active second then memory_cell_pair_address_check locations
          (activated_cell first) (activated_cell second) else true else true)).
    rewrite conditional_known by exact FIRST_TEST.
    destruct (active first) eqn:FIRST; cbn.
    + change (command_run decision_test_language
        (conditional decision_test_language (activated_test second)
          (memory_cell_pair_address_tree code (activated_cell first) (activated_cell second)) (Decision true))
        s flag <-> flag = (if active second then memory_cell_pair_address_check locations
          (activated_cell first) (activated_cell second) else true)).
      rewrite conditional_known by exact SECOND_TEST.
      destruct (active second) eqn:SECOND; cbn.
      * apply memory_cell_pair_address_exact; [apply FIRST_ADDRESS; exact FIRST|apply SECOND_ADDRESS; exact SECOND].
      * split; [intro RUN; inversion RUN; reflexivity|intro EQUAL; subst; constructor].
    + split; [intro RUN; inversion RUN; reflexivity|intro EQUAL; subst; constructor].
Qed.
Fixpoint memory_activated_tail_tree code first rest := match rest with
  | [] => Decision true
  | second::rest => decision_bind (memory_activated_pair_tree code first second)
      (memory_activated_tail_tree code first rest) (Decision false) end.
Fixpoint memory_activated_alias_tree code items := match items with
  | [] => Decision true
  | first::rest => decision_bind (memory_activated_tail_tree code first rest)
      (memory_activated_alias_tree code rest) (Decision false) end.
Fixpoint memory_activated_alias_check locations active items := match items with
  | [] => true
  | first::rest => forallb (memory_activated_pair_check locations active first) rest &&
      memory_activated_alias_check locations active rest end.
Definition memory_activated_item_domain code locations s active item :=
  memory_activation_exact s active item /\ memory_activated_address_binding code locations s active item.
Lemma memory_activated_tail_exact code locations s active first items :
  memory_activated_item_domain code locations s active first ->
  Forall (memory_activated_item_domain code locations s active) items ->
  forall flag, decision_run s (memory_activated_tail_tree code first items) flag <->
    flag = forallb (memory_activated_pair_check locations active first) items.
Proof.
  intros [FIRST_TEST FIRST_ADDRESS] ITEMS; induction ITEMS as [|item items [TEST ADDRESS] ITEMS IH];
    intro flag; cbn.
  - split; [intro RUN; inversion RUN; reflexivity|intro EQUAL; subst; constructor].
  - apply memory_decision_bind_exact.
    + apply memory_activated_pair_exact; assumption.
    + exact IH.
Qed.
Theorem memory_activated_alias_exact code locations s active items :
  Forall (memory_activated_item_domain code locations s active) items ->
  forall flag, decision_run s (memory_activated_alias_tree code items) flag <->
    flag = memory_activated_alias_check locations active items.
Proof.
  intro ITEMS; induction ITEMS; intro flag; cbn.
  - split; [intro RUN; inversion RUN; reflexivity|intro EQUAL; subst; constructor].
  - apply memory_decision_bind_exact; [apply memory_activated_tail_exact; assumption|exact IHITEMS].
Qed.
Lemma memory_activated_tail_selected locations active first items :
  active first = true ->
  forallb (memory_activated_pair_check locations active first) items =
    forallb (memory_cell_pair_address_check locations (activated_cell first)) (memory_selected_cells active items).
Proof.
  intro FIRST; unfold memory_selected_cells; induction items; cbn; [reflexivity|].
  unfold memory_activated_pair_check at 1; rewrite FIRST.
  destruct (active a) eqn:ACTIVE; cbn; rewrite IHitems; reflexivity.
Qed.
Theorem memory_activated_alias_selected_check locations active items :
  memory_activated_alias_check locations active items =
    memory_finite_address_check locations (memory_selected_cells active items).
Proof.
  induction items as [|item items IH]; cbn; [reflexivity|].
  destruct (active item) eqn:ACTIVE; cbn.
  - rewrite memory_activated_tail_selected by exact ACTIVE; rewrite IH; reflexivity.
  - assert (SKIP : forallb (memory_activated_pair_check locations active item) items = true).
    { apply forallb_forall; intros other MEMBER; unfold memory_activated_pair_check; rewrite ACTIVE; reflexivity. }
    rewrite SKIP; cbn; exact IH.
Qed.
Theorem memory_activated_selected_bindings code locations s active items :
  Forall (memory_activated_item_domain code locations s active) items ->
  Forall (memory_cell_address_binding code locations s) (memory_selected_cells active items).
Proof.
  intro DOMAIN; apply Forall_forall; intros cell MEMBER; unfold memory_selected_cells in MEMBER.
  apply in_map_iff in MEMBER as [item [SAME MEMBER]]; subst cell.
  apply filter_In in MEMBER as [MEMBER ACTIVE].
  apply Forall_forall with (x := item) in DOMAIN; [|exact MEMBER].
  destruct DOMAIN as [TEST ADDRESS]; apply ADDRESS; exact ACTIVE.
Qed.
Theorem memory_activated_alias_condition_sound code locations s active items :
  Forall (memory_activated_item_domain code locations s active) items ->
  decision_run s (memory_activated_alias_tree code items) true ->
  locations_nonalias (memory_restrict_locations (memory_footprint_allowed (memory_selected_cells active items)) locations).
Proof.
  intros DOMAIN RUN; apply memory_restricted_locations_nonalias.
  apply (@memory_finite_address_separation_sound code locations s _
    (@memory_activated_selected_bindings code locations s active items DOMAIN)).
  rewrite <-memory_activated_alias_selected_check.
  symmetry; exact (proj1 (@memory_activated_alias_exact code locations s active items DOMAIN true) RUN).
Qed.
Print Assumptions memory_activated_alias_exact.
Print Assumptions memory_activated_alias_selected_check.
Print Assumptions memory_activated_alias_condition_sound.
