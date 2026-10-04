From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Coqlib Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCountedLoop ClightTempFrame ClightLoopSyntax ClightRegionProgress ClightFrontendLoopProtocol.
From GuardMemory Require Import GuardMemoryControlSettle GuardMemorySettledCountedLoop
  GuardMemoryRecursiveSource GuardMemoryRecursiveFramedExecution GuardMemoryNaryLoops GuardMemoryNaryLift.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Theorem memory_started_source_decode_framed fe ge locals iterator bound body child protected (capability : temp_env -> Prop) :
  (forall before after, temp_agree protected before after -> capability before -> capability after) ->
  memory_nest_shapes (MemorySourceAxis iterator bound body child) ->
  memory_nest_fresh (MemorySourceAxis iterator bound body child) ->
  (forall identifier, In identifier (memory_nest_iterators (MemorySourceAxis iterator bound body child)) -> ~ In identifier protected) ->
  normal_statement (memory_nest_leaf child) = true -> quiet_statement (memory_nest_leaf child) = true ->
  writes_only [] (memory_nest_leaf child) ->
  forall upper count counts start (point : list Z -> mem -> mem -> Prop)
    prefix_ids prefix temps memory after final,
    length counts = length (memory_nest_iterators child) ->
    Forall (fun n => n <> O /\ signed_range (Z.of_nat n)) counts ->
    count <> O -> 0 < Z.of_nat upper -> signed_range (Z.of_nat upper) ->
    signed_range start -> Z.of_nat upper = start + Z.of_nat count ->
    (forall identifier, In identifier (memory_nest_iterators (MemorySourceAxis iterator bound body child)) ->
      ~ In identifier prefix_ids) ->
    (forall values le before next target,
      (exists x, start <= x < Z.of_nat upper /\ memory_nary_domain counts (prefix++[x]) values) ->
      memory_nest_bindings (prefix_ids++memory_nest_iterators (MemorySourceAxis iterator bound body child)) values le -> capability le ->
      exec_stmt fe ge locals le before (memory_nest_leaf child) E0 next target Out_normal ->
      point values before target /\ next = le) ->
    memory_nest_bindings prefix_ids prefix temps ->
    memory_nest_bindings (memory_nest_bounds (MemorySourceAxis iterator bound body child))
      (map Z.of_nat (upper::counts)) temps ->
    temps ! iterator = Some (Vint (Int.repr start)) -> capability temps ->
    exec_stmt fe ge locals temps memory (frontend_counted_loop iterator bound body) E0 after final Out_normal ->
    counted_iterations (fun x => memory_nary_iterations point counts (prefix++[x])) count start memory final /\
    after = memory_nest_exit (MemorySourceAxis iterator bound body child) (upper::counts) temps.
Proof.
  intros CAPABILITY_FRAME SHAPES FRESH PROTECTED NORMAL QUIET WRITES upper count counts start point prefix_ids prefix temps memory after final
    LENGTH COUNTS POSITIVE UPPER_POSITIVE UPPER_RANGE START_RANGE SPAN PREFIX_FRESH DECODE PREFIX BOUNDS INITIAL CAPABILITY SOURCE.
    assert (CHILD_FRESH : memory_nest_fresh child /\ ~ In iterator (memory_nest_iterators child) /\
      ~ In bound (memory_nest_iterators child) /\ iterator <> bound).
    { apply memory_nest_fresh_child with (body := body); exact FRESH. }
    destruct CHILD_FRESH as [CHILD_FRESH [ITERATOR_FRESH [BOUND_FRESH DISTINCT]]].
    assert (CHILD_LENGTH : length counts = length (memory_nest_iterators child)) by exact LENGTH.
    inversion BOUNDS as [|same value identifiers values BOUND CHILD_BOUNDS]; subst same value identifiers values.
    assert (BODY_NORMAL : normal_statement body = true).
    { eapply memory_nest_body_normal; eassumption. }
    assert (BODY_WRITES : writes_only (memory_nest_iterators child) body).
    { eapply memory_nest_body_writes; eassumption. }
    assert (EXIT : memory_nest_exit (MemorySourceAxis iterator bound body child) (upper::counts) temps =
      settled_exit (memory_nest_exit child counts) iterator temps count (Z.of_nat upper)).
    { destruct count; [contradiction|]. destruct upper; [cbn in UPPER_POSITIVE; lia|reflexivity]. }
    rewrite EXIT;
    eapply frontend_settled_decode with (written := memory_nest_iterators child)
      (settle := memory_nest_exit child counts) (floor := start)
      (stable := prefix_ids++memory_nest_bounds child++protected) (base := temps).
    + intros le key NOT_WRITTEN; unfold memory_nest_exit; apply memory_settle_controls_frame.
      rewrite memory_nest_assignment_keys by exact CHILD_LENGTH; exact NOT_WRITTEN.
    + intro le; apply memory_settle_controls_idempotent.
    + intros le value; unfold memory_nest_exit; apply memory_settle_controls_commute.
      rewrite memory_nest_assignment_keys by exact CHILD_LENGTH; exact ITERATOR_FRESH.
    + exact DISTINCT.
    + split; assumption.
    + intro MEMBER; apply in_app_or in MEMBER as [MEMBER|MEMBER].
      * apply (PREFIX_FRESH iterator ltac:(cbn; auto)); exact MEMBER.
      * apply in_app_or in MEMBER as [MEMBER|MEMBER].
        -- apply (proj2 FRESH iterator ltac:(cbn; auto)); cbn; auto.
        -- apply (PROTECTED iterator ltac:(cbn; auto)); exact MEMBER.
    + intros identifier MEMBER WRITTEN; apply in_app_or in MEMBER as [MEMBER|MEMBER].
      * apply (PREFIX_FRESH identifier ltac:(cbn; auto)); exact MEMBER.
      * apply in_app_or in MEMBER as [MEMBER|MEMBER].
        -- apply (proj2 CHILD_FRESH identifier WRITTEN); exact MEMBER.
        -- apply (PROTECTED identifier ltac:(cbn; auto)); exact MEMBER.
    + exact BODY_NORMAL.
    + exact BODY_WRITES.
    + exact UPPER_RANGE.
    + intros x le before next target X ITER BOUND' FRAME EXEC.
      assert (PREFIX_LE : memory_nest_bindings prefix_ids prefix le).
      { eapply memory_nest_bindings_frame_from; [intros id M; apply in_or_app; left; exact M|exact FRAME|exact PREFIX]. }
      assert (INNER_BOUNDS : memory_nest_bindings (memory_nest_bounds child) (map Z.of_nat counts) le).
      { eapply memory_nest_bindings_frame_from; [intros id M; apply in_or_app; right; apply in_or_app; left; exact M|exact FRAME|exact CHILD_BOUNDS]. }
      assert (INNER_PREFIX : memory_nest_bindings (prefix_ids++[iterator]) (prefix++[x]) le).
      { apply memory_nest_bindings_append; [exact PREFIX_LE|constructor; [exact ITER|constructor]]. }
      assert (INNER_FRESH : forall identifier, In identifier (memory_nest_iterators child) ->
        ~ In identifier (prefix_ids++[iterator])).
      { intros identifier MEMBER BAD; apply in_app_or in BAD as [BAD|BAD].
        - apply (PREFIX_FRESH identifier ltac:(cbn; auto)); exact BAD.
        - cbn in BAD; destruct BAD as [SAME|[]]; subst; contradiction. }
      assert (BODY_SHAPE : memory_nest_child_shape body child) by exact (proj1 SHAPES).
      pose proof (@memory_nest_child_decode fe ge locals body child le before next target BODY_SHAPE EXEC) as INNER.
      assert (CHILD_PROTECTED : forall identifier, In identifier (memory_nest_iterators child) -> ~ In identifier protected).
      { intros identifier MEMBER; apply PROTECTED; cbn; auto. }
      assert (CAP_LE : capability le).
      { eapply CAPABILITY_FRAME; [|exact CAPABILITY].
        eapply temp_agree_weaken; [|exact FRAME].
        intros identifier MEMBER; apply in_or_app; right; apply in_or_app; right; exact MEMBER. }
      assert (CAP_CHILD : capability (memory_nest_child_temps child le)).
      { eapply CAPABILITY_FRAME; [apply memory_nest_child_frame; exact CHILD_PROTECTED|exact CAP_LE]. }
      destruct (@memory_recursive_source_decode_framed fe ge locals child protected capability CAPABILITY_FRAME
        (proj2 SHAPES) CHILD_FRESH CHILD_PROTECTED NORMAL QUIET WRITES counts point
        (prefix_ids++[iterator]) (prefix++[x]) (memory_nest_child_temps child le) before next target
        CHILD_LENGTH COUNTS INNER_FRESH) as [POINT EXIT'];
        [| | | |exact CAP_CHILD|exact INNER|].
      * intros values current initial final_temps final_memory DOMAIN WORDS CAP_CURRENT RUN.
        apply DECODE; [exists x; split; [exact X|exact DOMAIN]| |exact CAP_CURRENT|exact RUN].
        rewrite <- app_assoc in WORDS; cbn [app] in WORDS; exact WORDS.
      * eapply memory_nest_bindings_frame; [apply memory_nest_child_frame; exact INNER_FRESH|exact INNER_PREFIX].
      * eapply memory_nest_bindings_frame; [apply memory_nest_child_frame; exact (proj2 CHILD_FRESH)|exact INNER_BOUNDS].
      * apply memory_nest_child_initial.
      * split; [exact POINT|rewrite EXIT',memory_nest_child_exit by exact CHILD_LENGTH; reflexivity].
    + exact SPAN.
    + exact START_RANGE.
    + lia.
    + exact INITIAL.
    + exact BOUND.
    + apply temp_agree_refl.
    + exact SOURCE.
Qed.
Print Assumptions memory_started_source_decode_framed.
