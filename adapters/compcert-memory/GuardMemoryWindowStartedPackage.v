From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From GuardMemory Require Import GuardMemoryRecursiveSource.
From GuardMemory Require Import GuardMemoryWindowPackage.
Set Implicit Arguments.
Record window_started_package (source : statement) := WindowStartedPackage {
  window_started_base : window_region_package source;
  window_started_iterator : ident;
  window_started_bound : ident;
  window_started_body : statement;
  window_started_child : memory_source_nest;
  window_started_nest : window_region_nest window_started_base =
    MemorySourceAxis window_started_iterator window_started_bound window_started_body window_started_child
}.
Definition make_window_started_package source (package : window_region_package source) : option (window_started_package source).
Proof.
  remember (window_region_nest package) as nest eqn:NEST.
  destruct nest as [leaf|iterator bound body child]; [exact None|].
  exact (Some (@WindowStartedPackage source package iterator bound body child (eq_sym NEST))).
Defined.
