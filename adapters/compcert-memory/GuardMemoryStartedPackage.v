From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Integers.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRecursiveSource GuardMemoryRecursiveDomain GuardMemoryScalarLoops
  GuardMemoryParamPointerSyntax GuardMemoryParamPointerProjectedCandidate.
From GuardMemory Require Import GuardMemoryStartedScalarLoop.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Record memory_started_pointer_package source := MemoryStartedPointerPackage {
  started_pointer_package : memory_param_pointer_region_package source;
  started_pointer_iterator : ident;
  started_pointer_bound : ident;
  started_pointer_body : statement;
  started_pointer_child : memory_source_nest;
  started_pointer_nest : param_pointer_region_nest started_pointer_package =
    MemorySourceAxis started_pointer_iterator started_pointer_bound started_pointer_body started_pointer_child
}.
Definition memory_started_pointer_context source (package : memory_started_pointer_package source) :=
  memory_param_pointer_runtime_context (started_pointer_package package)++[started_pointer_iterator package].
Definition memory_started_pointer_loop source (package : memory_started_pointer_package source) :=
  memory_started_scalar_loop (length (memory_nest_iterators (param_pointer_region_nest (started_pointer_package package))))
    (length (param_pointer_region_parameters (started_pointer_package package)++param_pointer_region_scalars (started_pointer_package package)))
    (memory_param_pointer_region_instructions (started_pointer_package package)).
Definition memory_started_pointer_root_cap source (package : memory_started_pointer_package source) :=
  hd 1 (param_pointer_region_limits (started_pointer_package package)).
Lemma memory_started_pointer_root_cap_sound source (package : memory_started_pointer_package source) :
  0 < memory_started_pointer_root_cap package /\ signed_range (memory_started_pointer_root_cap package).
Proof.
  pose proof (param_pointer_region_limits_length (param_pointer_region_syntax (started_pointer_package package))) as LENGTH.
  rewrite (started_pointer_nest package) in LENGTH; cbn [memory_nest_iterators length] in LENGTH.
  unfold memory_started_pointer_root_cap.
  pose proof (param_pointer_region_caps (param_pointer_region_syntax (started_pointer_package package))) as CAPS.
  destruct (param_pointer_region_limits (started_pointer_package package)); [cbn in LENGTH; lia|].
  inversion CAPS; assumption.
Qed.
Print Assumptions memory_started_pointer_root_cap_sound.
