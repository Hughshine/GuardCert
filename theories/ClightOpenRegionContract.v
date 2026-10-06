From Stdlib Require Import List Arith.
From compcert.lib Require Import Maps.
From compcert.common Require Import AST Values Memory Events Smallstep.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightGuard ClightCondition ClightTempFootprint ClightTempFrame
  ClightRegionProgress CompCertMemoryEquivalence.
Set Implicit Arguments.

(** A local simulation can keep stepping forever. Only source steps that the
    target matches with zero steps must decrease the index. The language host
    supplies the actual surrounding functions, continuations and environments. *)
Definition open_region_exit live f tf k tk e source target :=
  exists le tle m tm,
    source = State f Sskip k e le m /\
    target = State tf Sskip tk e tle tm /\
    temp_agree live le tle /\ memory_equivalent m tm.

Record open_region_protocol live temps ge tge f tf k tk e original replacement := {
  open_match : nat -> state -> state -> Prop;
  open_initial : forall le tle m,
    statement_scope live original -> temp_agree live le tle ->
    exists index, open_match index
      (State f original k e le m) (State tf replacement tk e tle m);
  open_source_shape : forall index source target,
    open_match index source target ->
    exists code stack le m, source = State f code stack e le m;
  open_advance : forall index source target events next,
    open_match index source target -> adapter_step temps ge source events next ->
    exists next_index next_target,
      (plus (adapter_step temps) tge target events next_target \/
       (star (adapter_step temps) tge target events next_target /\ next_index < index)) /\
      (open_match next_index next next_target \/
       open_region_exit live f tf k tk e next next_target)
}.

(** A rule must work under any enclosing continuation and preserved globals.
    Neither a source termination proof nor a guard-independent loop rank is a
    field of this contract. Guard safety and conditional progress belong to the
    local protocol that establishes it. *)
Record open_region_contract live original replacement : Prop := {
  open_source_labels : label_free original = true;
  open_target_labels : label_free replacement = true;
  open_context_protocol : forall temps ge tge f tf k tk e,
    preserving_globals ge tge ->
    exists protocol : open_region_protocol live temps ge tge f tf k tk e original replacement, True
}.
