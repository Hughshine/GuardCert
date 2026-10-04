From GuardMemory Require Import GuardMemoryRecursiveSource GuardMemoryParamPointerSyntax.
From GuardMemory Require Import GuardMemoryStartedPackage.

Set Implicit Arguments.
Definition make_memory_started_pointer_package source (package : memory_param_pointer_region_package source)
  : option (memory_started_pointer_package source).
Proof.
  remember (param_pointer_region_nest package) as nest eqn:NEST.
  destruct nest as [leaf|iterator bound body child]; [exact None|].
  exact (Some (@MemoryStartedPointerPackage source package iterator bound body child (eq_sym NEST))).
Defined.
Print Assumptions make_memory_started_pointer_package.
