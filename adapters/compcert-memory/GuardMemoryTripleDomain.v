From Stdlib Require Import List ZArith Lia Bool.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightGuard ClightNoWrap ClightRedundantSet ClightCountedLoop
  ClightStraightLine ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops GuardMemoryMultipleArrays GuardMemoryRegistryBackend
  GuardMemoryNaryBodyModel GuardMemoryNaryLoops GuardMemoryTripleBody GuardMemoryTripleWords GuardMemoryTripleSyntax
  GuardMemoryTripleGuard GuardMemoryRegistryGuard.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_triple_parameters d temps := map (fun identifier => Int.signed (temp_word identifier temps))
  [triple_row_bound d;triple_column_bound d;triple_depth_bound d].
Definition memory_triple_exit d temps :=
  PTree.set (triple_row d) (Vint (temp_word (triple_row_bound d) temps))
    (PTree.set (triple_column d) (Vint (temp_word (triple_column_bound d) temps))
      (PTree.set (triple_depth d) (Vint (temp_word (triple_depth_bound d) temps)) temps)).

Theorem memory_triple_source_under_ranges source (package : memory_triple_region_package source) fe ge locals temps memory after final :
  temps ! (triple_row (triple_region_description package)) = Some (Vint Int.zero) ->
  register_range (triple_row_bound (triple_region_description package)) (triple_cap (triple_region_description package)) (Entry ge locals temps memory) ->
  register_range (triple_column_bound (triple_region_description package)) (triple_cap (triple_region_description package)) (Entry ge locals temps memory) ->
  register_range (triple_depth_bound (triple_region_description package)) (triple_cap (triple_region_description package)) (Entry ge locals temps memory) ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  exists entries,
    Forall2 (memory_descriptor_binding ge locals) (memory_triple_region_descriptors package) entries /\
    NoDup (map memory_array_id entries) /\
    Forall (fun entry => Mem.valid_pointer memory (memory_array_block entry) 0 = true) entries /\
    L.loop_semantics (memory_nary_rectangle 0 3 (memory_triple_region_instructions package))
      (memory_triple_parameters (triple_region_description package) temps)
      (RuntimeState (memory_array_registry entries) memory) (RuntimeState (memory_array_registry entries) final) /\
    after = memory_triple_exit (triple_region_description package) temps.
Proof.
  destruct package as [d CERT]; destruct CERT as [SOURCE MODEL CAP MIDDLE OUTER RC RD RN RM RL CD CM CL CN DL DM DN].
  cbn in *; subst source; intros ZERO [[n NLOOK] NRANGE] [[m MLOOK] MRANGE] [[l LLOOK] LRANGE] RUN.
  cbn [entry_temps] in NLOOK,MLOOK,LLOOK,NRANGE,MRANGE,LRANGE.
  unfold temp_word in NRANGE,MRANGE,LRANGE; rewrite NLOOK in NRANGE; rewrite MLOOK in MRANGE; rewrite LLOOK in LRANGE.
  set (rows := Z.to_nat (Int.signed n)); set (columns := Z.to_nat (Int.signed m)); set (depths := Z.to_nat (Int.signed l)).
  assert (RZ : Z.of_nat rows = Int.signed n) by (unfold rows; apply Z2Nat.id; lia).
  assert (CZ : Z.of_nat columns = Int.signed m) by (unfold columns; apply Z2Nat.id; lia).
  assert (DZ : Z.of_nat depths = Int.signed l) by (unfold depths; apply Z2Nat.id; lia).
  destruct (@memory_triple_body_source_decode fe ge locals (triple_row d) (triple_row_bound d)
    (triple_column d) (triple_column_bound d) (triple_depth d) (triple_depth_bound d)
    (triple_cap d) (triple_cap d) (triple_cap d) (triple_body d) (triple_middle_body d) (triple_outer_body d)
    MODEL rows columns depths temps memory after final RC RD RN RM RL CD CM CL CN DL DM DN
    ltac:(rewrite RZ; apply Int.signed_range) ltac:(rewrite CZ; apply Int.signed_range) ltac:(rewrite DZ; apply Int.signed_range)
    ltac:(rewrite RZ; exact NRANGE) ltac:(rewrite CZ; exact MRANGE) ltac:(rewrite DZ; exact LRANGE)
    MIDDLE OUTER ZERO ltac:(rewrite RZ,Int.repr_signed; exact NLOOK)
    ltac:(rewrite CZ,Int.repr_signed; exact MLOOK) ltac:(rewrite DZ,Int.repr_signed; exact LLOOK) RUN)
    as [entries [ARRAYS [UNIQUE [POINTERS [LOOP EXIT]]]]].
  exists entries; split; [exact ARRAYS|]; split; [exact UNIQUE|]; split; [exact POINTERS|]; split.
  - unfold memory_triple_parameters; cbn [map]; unfold temp_word; rewrite NLOOK,MLOOK,LLOOK.
    rewrite RZ,CZ,DZ in LOOP; exact LOOP.
  - rewrite EXIT,RZ,CZ,DZ,!Int.repr_signed; unfold memory_triple_exit,temp_word; rewrite NLOOK,MLOOK,LLOOK; reflexivity.
Qed.

Theorem memory_triple_region_source_domain source (package : memory_triple_region_package source) fe ge locals temps memory after final :
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  memory_triple_guard_domain (triple_cap (triple_region_description package)) (memory_triple_region_descriptors package)
    (triple_row (triple_region_description package)) (triple_row_bound (triple_region_description package))
    (triple_column_bound (triple_region_description package)) (triple_depth_bound (triple_region_description package))
    (Entry ge locals temps memory).
Proof.
  intro RUN; pose proof (triple_region_syntax package) as CERT.
  destruct CERT as [SOURCE MODEL [POS CAP] MIDDLE OUTER RC RD RN RM RL CD CM CL CN DL DM DN].
  rewrite SOURCE in RUN.
  destruct (@memory_triple_source_words fe ge locals
    (triple_row (triple_region_description package)) (triple_row_bound (triple_region_description package))
    (triple_column (triple_region_description package)) (triple_column_bound (triple_region_description package))
    (triple_depth (triple_region_description package)) (triple_depth_bound (triple_region_description package))
    (triple_body (triple_region_description package)) (triple_middle_body (triple_region_description package))
    (triple_outer_body (triple_region_description package)) temps memory after final
    RC RD ltac:(congruence) ltac:(congruence) CD ltac:(congruence) ltac:(congruence) ltac:(congruence) ltac:(congruence)
    (nary_body_quiet MODEL) (nary_body_writes MODEL) MIDDLE OUTER RUN) as [ROW [BOUND CONTINUATION]].
  split; [exact ROW|]; split; [exact BOUND|]; intro HEADER.
  destruct (memory_triple_header_sound CAP ROW BOUND HEADER) as [ZERO NRANGE].
  destruct (CONTINUATION ZERO (proj1 (proj2 NRANGE))) as [COLUMN REST].
  split; [exact COLUMN|]; intro WIDTH.
  pose proof (register_range_sound CAP COLUMN WIDTH) as MRANGE.
  pose proof (REST (proj1 (proj2 MRANGE))) as DEPTH.
  split; [exact DEPTH|]; intro LENGTH.
  pose proof (register_range_sound CAP DEPTH LENGTH) as LRANGE.
  rewrite <- SOURCE in RUN.
  destruct (@memory_triple_source_under_ranges source package fe ge locals temps memory after final
    ZERO NRANGE MRANGE LRANGE RUN) as [entries [ARRAYS [UNIQUE [POINTERS REST']]]].
  exists entries; split; assumption.
Qed.
Print Assumptions memory_triple_source_under_ranges.
Print Assumptions memory_triple_region_source_domain.
