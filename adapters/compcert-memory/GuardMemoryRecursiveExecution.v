From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Coqlib Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCountedLoop ClightTempFrame ClightLoopSyntax ClightRegionProgress.
From GuardMemory Require Import GuardMemoryControlSettle GuardMemorySettledCountedLoop
  GuardMemoryRecursiveSource GuardMemoryNaryLoops GuardMemoryNaryLift.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Theorem memory_recursive_source_decode fe ge locals nest :
  memory_nest_shapes nest -> memory_nest_fresh nest ->
  normal_statement (memory_nest_leaf nest) = true -> quiet_statement (memory_nest_leaf nest) = true ->
  writes_only [] (memory_nest_leaf nest) ->
  forall counts (point : list Z -> mem -> mem -> Prop) prefix_ids prefix temps memory after final,
    length counts = length (memory_nest_iterators nest) ->
    Forall (fun count => count <> O /\ signed_range (Z.of_nat count)) counts ->
    (forall identifier, In identifier (memory_nest_iterators nest) -> ~ In identifier prefix_ids) ->
    (forall values le before next target, memory_nary_domain counts prefix values ->
      memory_nest_bindings (prefix_ids++memory_nest_iterators nest) values le ->
      exec_stmt fe ge locals le before (memory_nest_leaf nest) E0 next target Out_normal ->
      point values before target /\ next = le) ->
    memory_nest_bindings prefix_ids prefix temps ->
    memory_nest_bindings (memory_nest_bounds nest) (map Z.of_nat counts) temps ->
    memory_nest_initial nest temps ->
    exec_stmt fe ge locals temps memory (memory_nest_source nest) E0 after final Out_normal ->
    memory_nary_iterations point counts prefix memory final /\ after = memory_nest_exit nest counts temps.
Proof.
  induction nest as [code|iterator bound body child IH];
    intros SHAPES FRESH NORMAL QUIET WRITES counts point prefix_ids prefix temps memory after final
      LENGTH COUNTS PREFIX_FRESH DECODE PREFIX BOUNDS INITIAL SOURCE.
  - destruct counts; cbn in LENGTH; [|discriminate].
    cbn [memory_nary_iterations memory_nest_exit memory_nest_assignments memory_settle_controls].
    apply DECODE; [reflexivity|rewrite app_nil_r; exact PREFIX|exact SOURCE].
  - assert (CHILD_FRESH : memory_nest_fresh child /\ ~ In iterator (memory_nest_iterators child) /\
      ~ In bound (memory_nest_iterators child) /\ iterator <> bound).
    { apply memory_nest_fresh_child with (body := body); exact FRESH. }
    destruct CHILD_FRESH as [CHILD_FRESH [ITERATOR_FRESH [BOUND_FRESH DISTINCT]]].
    destruct counts as [|count counts]; cbn [memory_nest_iterators length] in LENGTH; [discriminate|].
    assert (CHILD_LENGTH : length counts = length (memory_nest_iterators child)) by lia.
    inversion COUNTS as [|same rest [POSITIVE RANGE] TAIL]; subst same rest.
    inversion BOUNDS as [|same value identifiers values BOUND CHILD_BOUNDS]; subst same value identifiers values.
    assert (BODY_NORMAL : normal_statement body = true).
    { eapply memory_nest_body_normal; eassumption. }
    assert (BODY_WRITES : writes_only (memory_nest_iterators child) body).
    { eapply memory_nest_body_writes; eassumption. }
    assert (EXIT : memory_nest_exit (MemorySourceAxis iterator bound body child) (count::counts) temps =
      settled_exit (memory_nest_exit child counts) iterator temps count (Z.of_nat count)).
    { destruct count; [contradiction|reflexivity]. }
    rewrite EXIT; cbn [memory_nary_iterations].
    eapply frontend_settled_decode with (written := memory_nest_iterators child)
      (settle := memory_nest_exit child counts) (floor := 0)
      (stable := prefix_ids++memory_nest_bounds child) (base := temps).
    + intros le key NOT_WRITTEN; unfold memory_nest_exit; apply memory_settle_controls_frame.
      rewrite memory_nest_assignment_keys by exact CHILD_LENGTH; exact NOT_WRITTEN.
    + intro le; apply memory_settle_controls_idempotent.
    + intros le value; unfold memory_nest_exit; apply memory_settle_controls_commute.
      rewrite memory_nest_assignment_keys by exact CHILD_LENGTH; exact ITERATOR_FRESH.
    + exact DISTINCT.
    + split; assumption.
    + intro MEMBER; apply in_app_or in MEMBER as [MEMBER|MEMBER].
      * apply (PREFIX_FRESH iterator ltac:(cbn; auto)); exact MEMBER.
      * apply (proj2 FRESH iterator ltac:(cbn; auto)); cbn; auto.
    + intros identifier MEMBER WRITTEN; apply in_app_or in MEMBER as [MEMBER|MEMBER].
      * apply (PREFIX_FRESH identifier ltac:(cbn; auto)); exact MEMBER.
      * apply (proj2 CHILD_FRESH identifier WRITTEN); exact MEMBER.
    + exact BODY_NORMAL.
    + exact BODY_WRITES.
    + exact RANGE.
    + intros x le before next target X ITER BOUND' FRAME EXEC.
      assert (PREFIX_LE : memory_nest_bindings prefix_ids prefix le).
      { eapply memory_nest_bindings_frame_from; [intros id M; apply in_or_app; left; exact M|exact FRAME|exact PREFIX]. }
      assert (INNER_BOUNDS : memory_nest_bindings (memory_nest_bounds child) (map Z.of_nat counts) le).
      { eapply memory_nest_bindings_frame_from; [intros id M; apply in_or_app; right; exact M|exact FRAME|exact CHILD_BOUNDS]. }
      assert (INNER_PREFIX : memory_nest_bindings (prefix_ids++[iterator]) (prefix++[x]) le).
      { apply memory_nest_bindings_append; [exact PREFIX_LE|constructor; [exact ITER|constructor]]. }
      assert (INNER_FRESH : forall identifier, In identifier (memory_nest_iterators child) ->
        ~ In identifier (prefix_ids++[iterator])).
      { intros identifier MEMBER BAD; apply in_app_or in BAD as [BAD|BAD].
        - apply (PREFIX_FRESH identifier ltac:(cbn; auto)); exact BAD.
        - cbn in BAD; destruct BAD as [SAME|[]]; subst; contradiction. }
      assert (BODY_SHAPE : memory_nest_child_shape body child) by exact (proj1 SHAPES).
      pose proof (@memory_nest_child_decode fe ge locals body child le before next target BODY_SHAPE EXEC) as INNER.
      destruct (IH (proj2 SHAPES) CHILD_FRESH NORMAL QUIET WRITES counts point
        (prefix_ids++[iterator]) (prefix++[x]) (memory_nest_child_temps child le) before next target
        CHILD_LENGTH TAIL INNER_FRESH) as [POINT EXIT'];
        [| | | |exact INNER|].
      * intros values current initial final_temps final_memory DOMAIN WORDS RUN.
        apply DECODE; [exists x; split; [exact X|exact DOMAIN]| |exact RUN].
        rewrite <- app_assoc in WORDS; cbn [app] in WORDS; exact WORDS.
      * eapply memory_nest_bindings_frame; [apply memory_nest_child_frame; exact INNER_FRESH|exact INNER_PREFIX].
      * eapply memory_nest_bindings_frame; [apply memory_nest_child_frame; exact (proj2 CHILD_FRESH)|exact INNER_BOUNDS].
      * apply memory_nest_child_initial.
      * split; [exact POINT|rewrite EXIT',memory_nest_child_exit by exact CHILD_LENGTH; reflexivity].
    + lia.
    + change (-2147483648 <= 0 <= 2147483647); lia.
    + lia.
    + exact INITIAL.
    + exact BOUND.
    + apply temp_agree_refl.
    + exact SOURCE.
Qed.
Print Assumptions memory_recursive_source_decode.
