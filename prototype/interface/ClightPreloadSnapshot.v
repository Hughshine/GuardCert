From Stdlib Require Import List.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightRedundantSet.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightSourceObservation
  ClightSourcePreloadObservation ClightAffineLoadedBoundTransport.
Import ListNotations.
Set Implicit Arguments.

(** A snapshot receipt may occur anywhere in a retained readonly prefix.
    Unique outputs and protected pointer bindings ensure its final value still
    denotes the observed cell. This does not assert future load stability. *)
Theorem source_preload_snapshot loads target pointer fe ge locals temps memory trace after final outcome :
  NoDup (source_load_targets loads) ->
  (forall identifier, In identifier (source_load_targets loads) ->
    ~ In identifier (source_load_pointers loads)) ->
  In (target,pointer) loads ->
  exec_stmt fe ge locals temps memory (source_load_prefix loads) trace after final outcome ->
  exists block offset value, after ! target = Some value /\
    after ! pointer = Some (Vptr block offset) /\
    Mem.loadv Mint32 final (Vptr block offset) = Some value.
Proof.
  revert temps trace after final outcome; induction loads as [|[head address] rest IH];
    intros temps trace after final outcome UNIQUE FRESH MEMBER RUN; [contradiction|].
  cbn [source_load_targets map fst] in UNIQUE; inversion UNIQUE as [|x xs NOT_REST UNIQUE_REST]; subst.
  destruct MEMBER as [SAME|MEMBER].
  - inversion SAME; subst head address.
    eapply (@source_preload_value target pointer rest fe ge locals temps memory trace after final outcome);
      [|exact NOT_REST| |exact RUN].
    + intro EQ; subst pointer; exact (FRESH target (or_introl eq_refl) (or_introl eq_refl)).
    + intro BAD; exact (FRESH pointer (or_intror BAD) (or_introl eq_refl)).
  - cbn [source_load_prefix] in RUN; inversion RUN; subst.
    2: match goal with SET : exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ |- _ => inversion SET; subst; contradiction end.
    match goal with SET : exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ |- _ => inversion SET; subst end.
    eapply IH; [assumption| |exact MEMBER|eassumption].
    intros identifier IN BAD; exact (FRESH identifier (or_intror IN) (or_intror BAD)).
Qed.

Definition loaded_preload_domain iterator cache pointer pointers entry :=
  register_domain iterator entry /\
  (exists word block offset,
    (entry_temps entry) ! cache = Some (Vint word) /\
    (entry_temps entry) ! pointer = Some (Vptr block offset) /\
    Mem.loadv Mint32 (entry_memory entry) (Vptr block offset) = Some (Vint word)) /\
  observed_pointer_domain pointers entry.

(** The first actual loaded header supplies integer typing even if a source
    preload initially returned Vundef. No optimization condition is assumed. *)
Theorem source_preload_loaded_domain loads iterator cache pointer pointers body
  fe ge locals temps memory middle after final :
  NoDup (source_load_targets loads) ->
  source_observations_check pointers loads = true -> In (cache,pointer) loads ->
  exec_stmt fe ge locals temps memory (source_load_prefix loads) E0 middle memory Out_normal ->
  exec_stmt fe ge locals middle memory (loaded_bound_loop iterator pointer body) E0 after final Out_normal ->
  loaded_preload_domain iterator cache pointer pointers (Entry ge locals middle memory).
Proof.
  intros UNIQUE CHECK MEMBER PREFIX SOURCE.
  destruct (@source_observations_check_sound pointers loads CHECK) as [COVER FRESH].
  destruct (@source_preload_snapshot loads cache pointer fe ge locals temps memory E0 middle memory Out_normal
    UNIQUE FRESH MEMBER PREFIX) as [block [offset [value [CACHE [POINTER READ]]]]].
  destruct (loaded_bound_completed_header SOURCE) as [flag TEST].
  destruct (loaded_bound_test_facts TEST) as [row [word [other [other_offset [ROW [OTHER [LOAD _]]]]]]].
  assert (SAME : Vptr other other_offset = Vptr block offset) by congruence.
  injection SAME as BLOCK OFFSET; subst other other_offset.
  assert (VALUE : value = Vint word) by congruence; subst value.
  split; [exists row; exact ROW|split; [exists word,block,offset; auto|]].
  destruct (@source_load_prefix_observations loads fe ge locals temps memory E0 middle memory Out_normal
    FRESH PREFIX) as [_ [_ [_ OBSERVED]]].
  intros identifier IN; apply OBSERVED,COVER; exact IN.
Qed.

Print Assumptions source_preload_snapshot.
Print Assumptions source_preload_loaded_domain.
