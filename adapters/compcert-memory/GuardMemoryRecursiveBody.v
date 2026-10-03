From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Coqlib Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCountedLoop ClightTempFrame ClightLoopSyntax ClightRegionProgress.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops
  GuardMemoryRegistryBackend GuardMemoryMultipleArrays GuardMemoryNaryRanges GuardMemoryNaryLoops
  GuardMemoryNaryLift GuardMemoryNaryBodyModel GuardMemoryRecursiveSource GuardMemoryRecursiveExecution.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma memory_nest_bindings_valuation identifiers values temps :
  NoDup identifiers -> memory_nest_bindings identifiers values temps ->
  exists valuation : ident -> Z, map valuation identifiers = values /\
    (forall identifier, In identifier identifiers -> temps ! identifier = Some (Vint (Int.repr (valuation identifier)))).
Proof.
  intros UNIQUE BINDINGS; revert UNIQUE; induction BINDINGS as [|identifier value identifiers values WORD BINDINGS IH]; intro UNIQUE.
  - exists (fun _ => 0); split; [reflexivity|cbn; tauto].
  - inversion UNIQUE; subst.
    destruct (IH ltac:(assumption)) as [valuation [VALUES WORDS]].
    exists (fun key => if peq key identifier then value else valuation key); split.
    + cbn [map]; destruct (peq identifier identifier); [|congruence].
      f_equal; rewrite <- VALUES; apply map_ext_in; intros key MEMBER.
      destruct (peq key identifier); [subst; contradiction|reflexivity].
    + intros key MEMBER; cbn in MEMBER; destruct MEMBER as [<-|MEMBER].
      * destruct (peq identifier identifier); [exact WORD|congruence].
      * destruct (peq key identifier); [subst; contradiction|apply WORDS; exact MEMBER].
Qed.
Lemma memory_nary_domain_suffix counts : forall prefix values,
  memory_nary_domain counts prefix values -> exists suffix, values = prefix++suffix /\
    Forall2 (fun count value => 0 <= value < Z.of_nat count) counts suffix.
Proof.
  induction counts as [|count counts IH]; intros prefix values DOMAIN; cbn [memory_nary_domain] in DOMAIN.
  - exists []; rewrite app_nil_r; split; [exact DOMAIN|constructor].
  - destruct DOMAIN as [value [RANGE DOMAIN]].
    destruct (IH _ _ DOMAIN) as [suffix [VALUES RANGES]].
    exists (value::suffix); split; [rewrite VALUES,<-app_assoc; reflexivity|constructor; assumption].
Qed.
Lemma memory_nary_domain_ranges counts limits values :
  Forall2 (fun count limit => Z.of_nat count <= limit) counts limits ->
  memory_nary_domain counts [] values -> memory_nary_ranges limits values.
Proof.
  intros LIMITS DOMAIN; destruct (@memory_nary_domain_suffix counts [] values DOMAIN) as [suffix [VALUES RANGES]]; cbn in VALUES; subst values.
  unfold memory_nary_ranges; clear DOMAIN; revert suffix RANGES; induction LIMITS; intros suffix RANGES.
  - inversion RANGES; constructor.
  - inversion RANGES; subst; constructor; [lia|apply IHLIMITS; assumption].
Qed.

Theorem memory_recursive_body_source_decode fe ge locals nest limits
  (model : memory_nary_body_model limits (memory_nest_iterators nest) (memory_nest_leaf nest))
  counts temps memory after final :
  memory_nest_shapes nest -> memory_nest_fresh nest ->
  length counts = length (memory_nest_iterators nest) ->
  Forall (fun count => count <> O /\ signed_range (Z.of_nat count)) counts ->
  Forall2 (fun count limit => Z.of_nat count <= limit) counts limits ->
  memory_nest_bindings (memory_nest_bounds nest) (map Z.of_nat counts) temps ->
  memory_nest_initial nest temps ->
  exec_stmt fe ge locals temps memory (memory_nest_source nest) E0 after final Out_normal ->
  exists entries,
    Forall2 (memory_descriptor_binding ge locals) (nary_body_descriptors model) entries /\
    NoDup (map memory_array_id entries) /\
    Forall (fun entry => Mem.valid_pointer memory (memory_array_block entry) 0 = true) entries /\
    L.loop_semantics (memory_nary_rectangle 0 (length counts) (nary_body_instructions model))
      (map Z.of_nat counts) (RuntimeState (memory_array_registry entries) memory)
        (RuntimeState (memory_array_registry entries) final) /\
    after = memory_nest_exit nest counts temps.
Proof.
  intros SHAPES FRESH LENGTH COUNTS LIMITS BOUNDS INITIAL SOURCE.
  set (physical := nary_body_point model ge locals).
  assert (DECODE : forall values le before next target, memory_nary_domain counts [] values ->
    memory_nest_bindings (memory_nest_iterators nest) values le ->
    exec_stmt fe ge locals le before (memory_nest_leaf nest) E0 next target Out_normal ->
    physical values before target /\ next = le).
  { intros values le before next target DOMAIN WORDS RUN.
    destruct (memory_nest_bindings_valuation (proj1 FRESH) WORDS) as [valuation [VALUES BINDINGS]].
    rewrite <- VALUES; eapply nary_body_decode.
    - rewrite VALUES; eapply memory_nary_domain_ranges; eassumption.
    - exact BINDINGS.
    - exact RUN. }
  destruct (@memory_recursive_source_decode fe ge locals nest SHAPES FRESH
    (nary_body_normal model) (nary_body_quiet model) (nary_body_writes model) counts physical [] []
    temps memory after final LENGTH COUNTS ltac:(cbn; tauto) DECODE ltac:(constructor) BOUNDS INITIAL SOURCE)
    as [ITER EXIT].
  assert (NONEMPTY : Forall (fun count => count <> O) counts).
  { eapply Forall_impl; [|exact COUNTS]; intros count [POS RANGE]; exact POS. }
  destruct (@memory_nary_first mem physical counts NONEMPTY [] memory final ITER) as [first HEAD].
  replace (length counts) with (length (memory_nest_iterators nest)) in HEAD by lia.
  destruct (@nary_body_registry _ _ _ model ge locals memory first HEAD) as [entries [ARRAYS [UNIQUE POINTERS]]].
  exists entries; split; [exact ARRAYS|]; split; [exact UNIQUE|]; split; [exact POINTERS|]; split; [|exact EXIT].
  apply (proj1 (@memory_nary_rectangle_lift (memory_array_registry entries) (nary_body_instructions model) physical
    counts memory final ltac:(intros values before target DOMAIN;
      apply nary_body_correspondence; [exact ARRAYS|exact UNIQUE|eapply memory_nary_domain_ranges; eassumption]))).
  exact ITER.
Qed.
Print Assumptions memory_recursive_body_source_decode.
