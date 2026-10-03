From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values.
From compcert.cfrontend Require Import Clight.
From Guard Require Import AbstractGuard SemanticFacts ClightCondition ClightPureExpr ClightGuard
  ClightRedundantSet ClightNoWrap ClightCountedLoop ClightRectangularGuard ClightMatrixGuard.
From GuardMemory Require Import GuardMemoryRegistryGuard GuardMemoryTripleGuard GuardMemoryRecursiveSource.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint memory_recursive_bounds_accept cap (bounds : list ident) s := match bounds with
  | [] => true | bound::rest => register_range_flag bound cap s && memory_recursive_bounds_accept cap rest s end.
Fixpoint memory_recursive_bounds_domain cap (bounds : list ident) s : Prop := match bounds with
  | [] => True
  | bound::rest => register_domain bound s /\
      (register_range_flag bound cap s = true -> memory_recursive_bounds_domain cap rest s) end.
Fixpoint memory_recursive_bounds_tree cap (bounds : list ident) terminal := match bounds with
  | [] => terminal
  | bound::rest => decision_bind (register_range_tree bound cap)
      (memory_recursive_bounds_tree cap rest terminal) (Decision false) end.
Theorem memory_recursive_bounds_exact cap bounds terminal s accepted :
  memory_recursive_bounds_domain cap bounds s ->
  (memory_recursive_bounds_accept cap bounds s = true -> forall flag, decision_run s terminal flag <-> flag = accepted) ->
  forall flag, decision_run s (memory_recursive_bounds_tree cap bounds terminal) flag <->
    flag = memory_recursive_bounds_accept cap bounds s && accepted.
Proof.
  induction bounds as [|bound bounds IH]; cbn [memory_recursive_bounds_domain memory_recursive_bounds_accept
    memory_recursive_bounds_tree]; intros DOMAIN TERMINAL flag.
  - apply TERMINAL; reflexivity.
  - destruct DOMAIN as [BOUND REST]; rewrite <- andb_assoc.
    apply memory_guard_gate_exact; [apply memory_triple_range_exact; exact BOUND|].
    intro RANGE; apply IH; [apply REST; exact RANGE|].
    intro ALL; apply TERMINAL; rewrite RANGE,ALL; reflexivity.
Qed.
Theorem memory_recursive_bounds_sound cap bounds s : signed_range cap ->
  memory_recursive_bounds_domain cap bounds s -> memory_recursive_bounds_accept cap bounds s = true ->
  Forall (fun bound => register_range bound cap s) bounds.
Proof.
  intro CAP; induction bounds as [|bound bounds IH]; cbn; intros DOMAIN ACCEPT; [constructor|].
  destruct DOMAIN as [BOUND REST]; apply andb_true_iff in ACCEPT as [RANGE ALL]; constructor.
  - apply register_range_sound; assumption.
  - apply IH; [apply REST; exact RANGE|exact ALL].
Qed.
Definition memory_recursive_guard_accept cap descriptors nest s := match nest with
  | MemorySourceLeaf _ => false
  | MemorySourceAxis iterator _ _ _ => register_flag iterator Int.zero s &&
      (memory_recursive_bounds_accept cap (memory_nest_bounds nest) s && memory_registry_guard_accept descriptors s) end.
Definition memory_recursive_guard_tree cap descriptors nest := match nest with
  | MemorySourceLeaf _ => Decision false
  | MemorySourceAxis iterator _ _ _ => decision_bind (register_tree iterator Int.zero)
      (memory_recursive_bounds_tree cap (memory_nest_bounds nest) (memory_array_registry_tree descriptors)) (Decision false) end.
Definition memory_recursive_guard_domain cap descriptors nest s : Prop := match nest with
  | MemorySourceLeaf _ => False
  | MemorySourceAxis iterator _ _ _ => register_domain iterator s /\
      (register_flag iterator Int.zero s = true -> memory_recursive_bounds_domain cap (memory_nest_bounds nest) s /\
        (memory_recursive_bounds_accept cap (memory_nest_bounds nest) s = true -> memory_registry_guard_domain descriptors s)) end.
Theorem memory_recursive_guard_exact cap descriptors nest s :
  memory_recursive_guard_domain cap descriptors nest s -> forall flag,
  decision_run s (memory_recursive_guard_tree cap descriptors nest) flag <->
    flag = memory_recursive_guard_accept cap descriptors nest s.
Proof.
  destruct nest; cbn [memory_recursive_guard_domain memory_recursive_guard_tree memory_recursive_guard_accept];
    intros DOMAIN flag; [contradiction|].
  destruct DOMAIN as [ITERATOR CONTINUATION]; apply memory_guard_gate_exact.
  - apply memory_triple_register_exact; exact ITERATOR.
  - intro ZERO; destruct (CONTINUATION ZERO) as [BOUNDS ARRAYS].
    apply memory_recursive_bounds_exact; [exact BOUNDS|].
    intro ALL; apply memory_registry_guard_exact; apply ARRAYS; exact ALL.
Qed.
Theorem memory_recursive_guard_sound cap descriptors nest s : signed_range cap ->
  memory_recursive_guard_domain cap descriptors nest s -> memory_recursive_guard_accept cap descriptors nest s = true ->
  memory_nest_initial nest (entry_temps s) /\ Forall (fun bound => register_range bound cap s) (memory_nest_bounds nest) /\
    memory_registry_guard_property descriptors s.
Proof.
  destruct nest; cbn [memory_recursive_guard_domain memory_recursive_guard_accept memory_nest_initial];
    intros CAP DOMAIN ACCEPT; [discriminate|].
  destruct DOMAIN as [ITERATOR CONTINUATION]; apply andb_true_iff in ACCEPT as [ZERO ACCEPT].
  apply andb_true_iff in ACCEPT as [ALL ALIAS]; destruct (CONTINUATION ZERO) as [BOUNDS ARRAYS].
  split; [eapply register_flag_evidence; eassumption|]; split.
  - eapply memory_recursive_bounds_sound; eassumption.
  - apply memory_registry_guard_accept_sound; [apply ARRAYS; exact ALL|exact ALIAS].
Qed.
Definition memory_recursive_guard_dimension cap descriptors nest :=
  @positive_dimension clight_entry unit (memory_recursive_guard_domain cap descriptors nest)
    (fun _ s => memory_recursive_guard_accept cap descriptors nest s = true)
    (fun _ => memory_recursive_guard_accept cap descriptors nest) (fun _ s _ ACCEPT => ACCEPT).
Definition memory_recursive_guard_primitives cap descriptors nest :
  check_primitives decision_test_language (memory_recursive_guard_domain cap descriptors nest)
    (decide_atom (memory_recursive_guard_dimension cap descriptors nest)).
Proof.
  refine (@CheckPrimitives clight_entry unit decision_test_language (memory_recursive_guard_domain cap descriptors nest)
    (decide_atom (memory_recursive_guard_dimension cap descriptors nest))
    (fun _ => memory_recursive_guard_tree cap descriptors nest) (fun _ => Decision true) _ _).
  - intros [] s flag DOMAIN.
    change (decision_run s (memory_recursive_guard_tree cap descriptors nest) flag <->
      flag = checked_valid (decide_atom (memory_recursive_guard_dimension cap descriptors nest) tt s)).
    rewrite memory_recursive_guard_exact by exact DOMAIN.
    cbn [memory_recursive_guard_dimension positive_dimension decide_atom];
      destruct (memory_recursive_guard_accept cap descriptors nest s); reflexivity.
  - intros [] s flag expected DOMAIN ACCEPT.
    change (decision_run s (Decision true) flag <-> flag = expected).
    cbn [memory_recursive_guard_dimension positive_dimension decide_atom] in ACCEPT.
    destruct (memory_recursive_guard_accept cap descriptors nest s); try discriminate;
      inversion ACCEPT; subst; split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor].
Defined.
Print Assumptions memory_recursive_guard_primitives.
