From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Csem.
From polcert.src Require Import Base PolyBase CTy CState.
From polcert.polygen Require Import InstrTy.
From Guard Require Import CompCertMemoryEquivalence.
Import ListNotations.
Open Scope Z_scope.
Set Implicit Arguments.

(** This view uses PolCert's concrete mutual-memory-extension relation. It
    does not identify memories by their representation or assume an abstract
    read/write oracle. The global environment is the source Csem environment;
    a Clight implementation may share its local blocks without sharing its
    function definitions. *)
Definition concrete_memory_view (ge : Csem.genv) (locals : Csem.env)
  (state : CState.t) (memory : mem) := CState.eq state (ge, locals, memory).

Lemma memory_view_refl ge locals memory :
  concrete_memory_view ge locals (ge, locals, memory) memory.
Proof. apply CState.eq_refl. Qed.

Lemma memory_view_state_eq ge locals source target memory :
  CState.eq source target -> concrete_memory_view ge locals source memory ->
  concrete_memory_view ge locals target memory.
Proof.
  intros EQ VIEW. unfold concrete_memory_view in *.
  eapply CState.eq_trans; [apply CState.eq_sym; exact EQ | exact VIEW].
Qed.

Lemma memory_eq_load chunk first second block offset value :
  CState.mem_eq first second -> Mem.load chunk first block offset = Some value ->
  Mem.load chunk second block offset = Some value.
Proof.
  intros EQ LOAD; exact (@memory_equivalent_load chunk block offset first second value EQ LOAD).
Qed.

Lemma memory_eq_store chunk first second block offset value first' :
  CState.mem_eq first second -> Mem.store chunk first block offset value = Some first' ->
  exists second', Mem.store chunk second block offset value = Some second' /\
    CState.mem_eq first' second'.
Proof.
  intros EQ STORE; exact (@memory_equivalent_store chunk block offset value first second first' EQ STORE).
Qed.

Lemma concrete_read_normalize ge locals source memory cell basetype value :
  concrete_memory_view ge locals source memory ->
  CState.read_cell cell basetype value source ->
  CState.read_cell cell basetype value (ge, locals, memory).
Proof. intros VIEW READ; eapply CState.read_cell_stable_under_eq; eauto. Qed.

(** A write relation permits equivalent source and result memories. Recover
    an actual store in the current memory and keep the result in the same
    concrete view. This closes the gap between State.eq and exact Clight
    memory transitions. *)
Lemma concrete_write_normalize ge locals memory target cell basetype value :
  CState.write_cell cell basetype value (ge, locals, memory) target ->
  exists memory' block ty arrayty offset chunk,
    CState.get_var_loc_type (ge, locals, memory) cell.(arr_id) = Some (block, ty) /\
    CTy.of_compcert_arrtype ty = Some arrayty /\
    CTy.basetype_of_arrtype arrayty = basetype /\
    CState.calc_offset arrayty cell.(arr_index) = Some offset /\
    CTy.basetype_access_mode basetype = By_value chunk /\
    Mem.store chunk memory block offset value = Some memory' /\
    concrete_memory_view ge locals target memory'.
Proof.
  intro WRITE.
  inversion WRITE as [cell0 v st st' st0 st0' id sub ge0 env0 m0 m0'
    b ty ofs aty bty chunk CELL ST LOOKUP ARRAY BASE OFFSET MODE STORE ST'
    EQ0 EQ1]; subst cell0 st st' st0 st0'.
  cbn [CState.eq] in EQ0.
  destruct EQ0 as [GE [ENV MEMORY]]; subst ge0 env0.
  subst cell.
  destruct (@memory_eq_store chunk m0 memory b ofs value m0' MEMORY STORE)
    as [memory' [STORE' RESULT]].
  exists memory', b, ty, aty, ofs, chunk. cbn.
  repeat split; try assumption.
  unfold concrete_memory_view.
  eapply CState.eq_trans; [apply CState.eq_sym; exact EQ1 |].
  cbn [CState.eq]; split; [reflexivity | split; [reflexivity | exact RESULT]].
Qed.

Print Assumptions concrete_read_normalize.
Print Assumptions concrete_write_normalize.
