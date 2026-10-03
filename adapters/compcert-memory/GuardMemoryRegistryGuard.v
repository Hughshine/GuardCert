From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps.
From compcert.common Require Import AST Values Memory Globalenvs.
From compcert.cfrontend Require Import Clight.
From Guard Require Import AbstractGuard SemanticFacts ClightCondition ClightPureExpr
  ClightRectangularStore.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryMultipleArrays
  GuardMemoryRegistryBackend GuardMemoryArraySeparation.
Import ListNotations.
Set Implicit Arguments.

Definition memory_blocks_distinct first rest := forallb (fun other => negb (Pos.eqb first other)) rest.
Fixpoint memory_blocks_unique blocks := match blocks with
  | [] => true
  | block::rest => memory_blocks_distinct block rest && memory_blocks_unique rest end.
Lemma memory_blocks_distinct_correct first rest :
  memory_blocks_distinct first rest = true <-> ~ In first rest.
Proof.
  unfold memory_blocks_distinct; rewrite forallb_forall; split.
  - intros DIFFERENT MEMBER; specialize (DIFFERENT first MEMBER); rewrite Pos.eqb_refl in DIFFERENT; discriminate.
  - intros ABSENT other MEMBER; apply negb_true_iff,Pos.eqb_neq; intro SAME; subst other; contradiction.
Qed.
Theorem memory_blocks_unique_correct blocks : memory_blocks_unique blocks = true <-> NoDup blocks.
Proof.
  induction blocks as [|block blocks IH]; cbn; [split; intro; constructor|].
  rewrite andb_true_iff,memory_blocks_distinct_correct,IH; split.
  - intros [FRESH REST]; constructor; assumption.
  - intro UNIQUE; inversion UNIQUE; auto.
Qed.

Definition memory_object_block variable s :=
  match (entry_env s) ! variable with
  | Some (block,_) => block
  | None => match Genv.find_symbol (entry_ge s) variable with Some block => block | None => 1%positive end
  end.
Definition memory_descriptor_block descriptor s := memory_object_block (memory_descriptor_variable descriptor) s.
Lemma memory_descriptor_block_binding descriptor entry s :
  memory_descriptor_binding (entry_ge s) (entry_env s) descriptor entry ->
  memory_descriptor_block descriptor s = memory_array_block entry.
Proof.
  intros [_ [_ [_ [LOCAL|[ABSENT GLOBAL]]]]]; unfold memory_descriptor_block,memory_object_block.
  - rewrite LOCAL; reflexivity.
  - rewrite ABSENT,GLOBAL; reflexivity.
Qed.
Lemma memory_descriptor_blocks_binding descriptors entries s :
  Forall2 (memory_descriptor_binding (entry_ge s) (entry_env s)) descriptors entries ->
  map (fun descriptor => memory_descriptor_block descriptor s) descriptors = map memory_array_block entries.
Proof.
  intro RELATED; induction RELATED; cbn; [reflexivity|].
  rewrite (@memory_descriptor_block_binding x y s H),IHRELATED; reflexivity.
Qed.

Fixpoint memory_array_tail_tree first rest := match rest with
  | [] => Decision true
  | second::rest => Test
      (memory_array_separation_test (memory_descriptor_shape first) (memory_descriptor_variable first)
        (memory_descriptor_shape second) (memory_descriptor_variable second))
      (memory_array_tail_tree first rest) (Decision false) end.
Fixpoint memory_array_registry_tree descriptors := match descriptors with
  | [] => Decision true
  | first::rest => decision_bind (memory_array_tail_tree first rest)
      (memory_array_registry_tree rest) (Decision false) end.

Lemma memory_decision_test_exact condition s known continuation accepted :
  (forall flag, expression_test condition s flag <-> flag = known) ->
  (forall flag, decision_run s continuation flag <-> flag = accepted) ->
  forall flag, decision_run s (Test condition continuation (Decision false)) flag <-> flag = known && accepted.
Proof.
  intros CONDITION REST flag.
  change (command_run decision_language (conditional decision_language condition continuation (Decision false)) s flag <-> flag = known && accepted).
  rewrite conditional_known by exact CONDITION.
  destruct known; cbn; [apply REST|].
  split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor].
Qed.
Lemma memory_decision_bind_exact first second s known accepted :
  (forall flag, decision_run s first flag <-> flag = known) ->
  (forall flag, decision_run s second flag <-> flag = accepted) ->
  forall flag, decision_run s (decision_bind first second (Decision false)) flag <-> flag = known && accepted.
Proof.
  intros FIRST SECOND flag.
  change (command_run decision_test_language
    (conditional decision_test_language first second (Decision false)) s flag <-> flag = known && accepted).
  rewrite conditional_known by exact FIRST.
  destruct known; cbn; [apply SECOND|].
  split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor].
Qed.

Lemma memory_array_tail_tree_exact first first_entry rest entries s :
  memory_descriptor_binding (entry_ge s) (entry_env s) first first_entry ->
  Mem.valid_pointer (entry_memory s) (memory_array_block first_entry) 0 = true ->
  Forall2 (memory_descriptor_binding (entry_ge s) (entry_env s)) rest entries ->
  Forall (fun entry => Mem.valid_pointer (entry_memory s) (memory_array_block entry) 0 = true) entries ->
  forall flag, decision_run s (memory_array_tail_tree first rest) flag <->
    flag = memory_blocks_distinct (memory_array_block first_entry) (map memory_array_block entries).
Proof.
  intros FIRST POINTER RELATED; induction RELATED as [|second entry rest entries BINDING RELATED IH];
    intros POINTERS flag; cbn [memory_array_tail_tree memory_blocks_distinct map forallb].
  - split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor].
  - inversion POINTERS as [|head tail VALID VALID_REST]; subst.
    apply memory_decision_test_exact.
    + destruct FIRST as [_ [_ [_ FIRST_ARRAY]]]; destruct BINDING as [_ [_ [_ SECOND_ARRAY]]].
      destruct s as [ge locals temps memory]; cbn in *.
      intro b; apply memory_array_separation_exact; assumption.
    + apply IH; exact VALID_REST.
Qed.
Theorem memory_array_registry_tree_exact descriptors entries s :
  Forall2 (memory_descriptor_binding (entry_ge s) (entry_env s)) descriptors entries ->
  Forall (fun entry => Mem.valid_pointer (entry_memory s) (memory_array_block entry) 0 = true) entries ->
  forall flag, decision_run s (memory_array_registry_tree descriptors) flag <->
    flag = memory_blocks_unique (map memory_array_block entries).
Proof.
  intro RELATED; induction RELATED as [|first entry rest entries BINDING RELATED IH];
    intros POINTERS flag; cbn [memory_array_registry_tree memory_blocks_unique map].
  - split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor].
  - inversion POINTERS as [|head tail VALID VALID_REST]; subst.
    apply memory_decision_bind_exact.
    + apply memory_array_tail_tree_exact with (first_entry := entry) (entries := entries); assumption.
    + apply IH; exact VALID_REST.
Qed.

Definition memory_registry_guard_domain descriptors s := exists entries,
  Forall2 (memory_descriptor_binding (entry_ge s) (entry_env s)) descriptors entries /\
  Forall (fun entry => Mem.valid_pointer (entry_memory s) (memory_array_block entry) 0 = true) entries.
Definition memory_registry_guard_property descriptors s := exists entries,
  Forall2 (memory_descriptor_binding (entry_ge s) (entry_env s)) descriptors entries /\
  NoDup (map memory_array_block entries).
Definition memory_registry_guard_accept descriptors s :=
  memory_blocks_unique (map (fun descriptor => memory_descriptor_block descriptor s) descriptors).
Theorem memory_registry_guard_accept_sound descriptors s :
  memory_registry_guard_domain descriptors s -> memory_registry_guard_accept descriptors s = true ->
  memory_registry_guard_property descriptors s.
Proof.
  intros [entries [ARRAYS POINTERS]] ACCEPT; exists entries; split; [exact ARRAYS|].
  apply memory_blocks_unique_correct; unfold memory_registry_guard_accept in ACCEPT.
  rewrite (@memory_descriptor_blocks_binding descriptors entries s ARRAYS) in ACCEPT; exact ACCEPT.
Qed.
Theorem memory_registry_guard_exact descriptors s :
  memory_registry_guard_domain descriptors s -> forall flag,
  decision_run s (memory_array_registry_tree descriptors) flag <-> flag = memory_registry_guard_accept descriptors s.
Proof.
  intros [entries [ARRAYS POINTERS]] flag; unfold memory_registry_guard_accept.
  rewrite (@memory_descriptor_blocks_binding descriptors entries s ARRAYS).
  apply memory_array_registry_tree_exact; assumption.
Qed.

Definition memory_registry_guard_dimension descriptors :=
  @positive_dimension clight_entry unit (memory_registry_guard_domain descriptors)
    (fun _ => memory_registry_guard_property descriptors) (fun _ => memory_registry_guard_accept descriptors)
    (fun _ => @memory_registry_guard_accept_sound descriptors).
Definition memory_registry_guard_primitives descriptors :
  check_primitives decision_test_language (memory_registry_guard_domain descriptors)
    (decide_atom (memory_registry_guard_dimension descriptors)).
Proof.
  refine (@CheckPrimitives clight_entry unit decision_test_language
    (memory_registry_guard_domain descriptors) (decide_atom (memory_registry_guard_dimension descriptors))
    (fun _ => memory_array_registry_tree descriptors) (fun _ => Decision true) _ _).
  - intros [] s flag DOMAIN.
    change (decision_run s (memory_array_registry_tree descriptors) flag <->
      flag = checked_valid (decide_atom (memory_registry_guard_dimension descriptors) tt s)).
    rewrite memory_registry_guard_exact by exact DOMAIN.
    cbn [memory_registry_guard_dimension positive_dimension decide_atom].
    destruct (memory_registry_guard_accept descriptors s); reflexivity.
  - intros [] s flag expected DOMAIN ACCEPT.
    change (decision_run s (Decision true) flag <-> flag = expected).
    cbn [memory_registry_guard_dimension positive_dimension decide_atom] in ACCEPT.
    destruct (memory_registry_guard_accept descriptors s); try discriminate; inversion ACCEPT; subst expected.
    split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor].
Defined.

Print Assumptions memory_blocks_unique_correct.
Print Assumptions memory_array_registry_tree_exact.
Print Assumptions memory_registry_guard_primitives.
