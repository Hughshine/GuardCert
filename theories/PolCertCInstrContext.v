From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Clight Csem.
From polcert.src Require Import CTy CState CInstr.
From polcert.polygen Require Import Loop.
From Guard Require Import PolCertReadOnlyContext CompCertMemoryEquivalence PolCertMemoryModel.
Import ListNotations.
Set Implicit Arguments.

(** This is an explicit new INSTR instance. It retains actual CInstr
    execution and its Bernstein proof, but obtains scalar context from
    temporaries and gives physical array compatibility existential witnesses.
    The locked legacy CState.valid and its theorems are not modified. *)
Module CInstrContext (Names : C_INSTR_NAMES).
Module Physical := CInstr Names.
Module PhysicalCompatibility <: CONTEXT_COMPATIBILITY Physical.
  Definition valid (id : Physical.ident) (ty : Physical.Ty.t) (state : Physical.State.t) : Prop :=
    let '(ge, locals, memory) := state in
    exists block ctype, Physical.State.get_var_loc_type state id = Some (block, ctype) /\
      Physical.Ty.of_compcert_arrtype ctype = Some ty /\
      Mem.range_perm memory block 0 (sizeof ge ctype) Cur Writable.
  Definition compatible declarations state :=
    Forall (fun decl => valid (fst decl) (snd decl) state) declarations.
End PhysicalCompatibility.
Module Context := ReadOnlyContext Physical PhysicalCompatibility.
Module L := Loop Context.

Definition temporary_snapshot (le : temp_env) (id : ident) : option Z :=
  match le ! id with Some (Vint word) => Some (Int.signed word) | _ => None end.
Definition context_state ge locals le memory : Context.State.t :=
  (temporary_snapshot le, (ge, locals, memory)).

Lemma defined_context_initializes names values ge locals le memory :
  Forall2 (fun id value => exists word, le ! id = Some (Vint word) /\ Int.signed word = value)
    names values -> Context.InitEnv names values (context_state ge locals le memory).
Proof.
  intro DEFINED; induction DEFINED; constructor; auto.
  destruct H as [word [LOOKUP VALUE]]; subst y.
  change (temporary_snapshot le x = Some (Int.signed word)).
  unfold temporary_snapshot; rewrite LOOKUP; reflexivity.
Qed.

Definition context_memory_view ge locals le (state : Context.State.t) memory : Prop :=
  (forall id, fst state id = temporary_snapshot le id) /\
    concrete_memory_view ge locals (snd state) memory.

Lemma context_memory_view_refl ge locals le memory :
  context_memory_view ge locals le (context_state ge locals le memory) memory.
Proof. split; [reflexivity | apply memory_view_refl]. Qed.

Lemma context_views_related ge locals le first second first_memory second_memory :
  Context.State.eq first second ->
  context_memory_view ge locals le first first_memory ->
  context_memory_view ge locals le second second_memory ->
  memory_equivalent first_memory second_memory.
Proof.
  intros [_ EQ] [_ FIRST] [_ SECOND].
  assert (MEMORY : CState.eq (ge, locals, first_memory) (ge, locals, second_memory)).
  { eapply CState.eq_trans; [apply CState.eq_sym; exact FIRST |].
    eapply CState.eq_trans; [exact EQ | exact SECOND]. }
  exact (proj2 (proj2 MEMORY)).
Qed.

Lemma physical_compatibility_has_witness id ty rest state :
  PhysicalCompatibility.compatible ((id,ty)::rest) state ->
  PhysicalCompatibility.valid id ty state.
Proof. intro COMPAT; inversion COMPAT; assumption. Qed.

Goal True. idtac "GUARDCERT_CONTEXT_BASELINE_BEGIN". exact Logic.I. Qed.
Print Assumptions Physical.bc_condition_implie_permutbility.
Goal True. idtac "GUARDCERT_CONTEXT_ADAPTER_BEGIN". exact Logic.I. Qed.
Print Assumptions defined_context_initializes.
Print Assumptions context_views_related.
Print Assumptions Context.bc_condition_implie_permutbility.
Goal True. idtac "GUARDCERT_CONTEXT_ASSUMPTIONS_END". exact Logic.I. Qed.
End CInstrContext.
