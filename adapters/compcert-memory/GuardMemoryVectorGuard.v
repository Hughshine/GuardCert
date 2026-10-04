From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Integers.
From compcert.common Require Import AST.
From Guard Require Import ClightCondition ClightPureExpr ClightGuard ClightNoWrap
  ClightCountedLoop ClightRedundantSet ClightRectangularGuard ClightMatrixGuard.
From GuardMemory Require Import GuardMemoryRecursiveSource GuardMemoryRecursiveGuard
  GuardMemoryRegistryGuard GuardMemoryTripleGuard.
From GuardMemory Require Import GuardMemoryVectorBounds.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_vector_guard_accept caps nest s :=
  match nest with
  | MemorySourceLeaf _ => false
  | MemorySourceAxis iterator _ _ _ => register_flag iterator Int.zero s &&
      memory_vector_bounds_accept caps (memory_nest_bounds nest) s end.
Definition memory_vector_guard_domain caps nest s : Prop :=
  match nest with
  | MemorySourceLeaf _ => True
  | MemorySourceAxis iterator _ _ _ => register_domain iterator s /\
      (register_flag iterator Int.zero s = true -> memory_vector_bounds_domain caps (memory_nest_bounds nest) s) end.
Definition memory_vector_guard_tree caps nest :=
  match nest with
  | MemorySourceLeaf _ => Decision false
  | MemorySourceAxis iterator _ _ _ => decision_bind (register_tree iterator Int.zero)
      (memory_vector_bounds_tree caps (memory_nest_bounds nest) (Decision true)) (Decision false) end.
Theorem memory_vector_guard_exact caps nest s :
  memory_vector_guard_domain caps nest s -> forall flag,
    decision_run s (memory_vector_guard_tree caps nest) flag <-> flag = memory_vector_guard_accept caps nest s.
Proof.
  destruct nest as [code|iterator bound body child]; cbn [memory_vector_guard_domain memory_vector_guard_tree memory_vector_guard_accept].
  - intros DOMAIN flag; split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor].
  - intros [ITERATOR BOUNDS] flag.
    replace (register_flag iterator Int.zero s && memory_vector_bounds_accept caps (memory_nest_bounds (MemorySourceAxis iterator bound body child)) s)
      with (register_flag iterator Int.zero s && memory_vector_bounds_accept caps (memory_nest_bounds (MemorySourceAxis iterator bound body child)) s && true) by (rewrite andb_true_r; reflexivity).
    rewrite <-andb_assoc; apply memory_guard_gate_exact; [apply memory_triple_register_exact; exact ITERATOR|].
    intro ZERO; apply memory_vector_bounds_exact; [apply BOUNDS; exact ZERO|].
    intros ALL result; split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor].
Qed.
Theorem memory_vector_guard_sound caps nest s :
  Forall signed_range caps -> memory_vector_guard_domain caps nest s -> memory_vector_guard_accept caps nest s = true ->
  memory_nest_initial nest (entry_temps s) /\
  Forall2 (fun cap bound => register_range bound cap s) caps (memory_nest_bounds nest).
Proof.
  destruct nest as [code|iterator bound body child]; cbn [memory_vector_guard_domain memory_vector_guard_accept]; [discriminate|].
  intros CAPS [ITERATOR BOUNDS] ACCEPT; apply andb_true_iff in ACCEPT as [ZERO ALL]; split.
  - exact (@register_flag_evidence iterator Int.zero s ITERATOR ZERO).
  - apply memory_vector_bounds_sound; [exact CAPS|apply BOUNDS; exact ZERO|exact ALL].
Qed.
Print Assumptions memory_vector_guard_exact.
Print Assumptions memory_vector_guard_sound.
