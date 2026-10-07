From Stdlib Require Import List ZArith.
From compcert.lib Require Import Integers.
From compcert.common Require Import Values.
From polcert.src Require Import PolyBase.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryDynamicTensorLayout.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The existing instruction semantics and dependence validator keep the whole
    affine coordinate vector. Dynamic layout enters only through the registry's
    physical nonalias law; the instruction computation still uses int32 values. *)
Theorem tensor_instruction_reorder array block base dimensions
    first first_parameters writes1 reads1 before middle after
    second second_parameters writes2 reads2 :
  tensor_layout_flag dimensions=true ->
  runtime_locations before=tensor_pointer_locations array block base dimensions ->
  GuardMemoryInstr.instr_semantics first first_parameters writes1 reads1 before middle ->
  GuardMemoryInstr.instr_semantics second second_parameters writes2 reads2 middle after ->
  Forall(fun write2=>Forall(fun write1=>cell_neq write1 write2)writes1)writes2 /\
  Forall(fun read2=>Forall(fun write1=>cell_neq write1 read2)writes1)reads2 /\
  Forall(fun write2=>Forall(fun read1=>cell_neq read1 write2)reads1)writes2 ->
  exists swapped final,
    GuardMemoryInstr.instr_semantics second second_parameters writes2 reads2 before swapped /\
    GuardMemoryInstr.instr_semantics first first_parameters writes1 reads1 swapped final /\
    GuardMemoryInstr.State.eq after final.
Proof.
  intros LAYOUT REGISTRY FIRST SECOND INDEPENDENT.
  eapply GuardMemoryInstr.bc_condition_implie_permutbility.
  - unfold GuardMemoryInstr.NonAlias,GuardMemoryInstr.State.non_alias; rewrite REGISTRY.
    apply tensor_pointer_locations_nonalias.
    exact(proj2(proj2(@tensor_layout_flag_sound dimensions LAYOUT))).
  - exact(conj FIRST SECOND).
  - exact INDEPENDENT.
Qed.

Print Assumptions tensor_instruction_reorder.
