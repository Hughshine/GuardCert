From Stdlib Require Import List ZArith RelationClasses.
From Guard Require Import AbstractSchedule.
From polcert.src Require Import PolyBase.
From polcert.polygen Require Import InstrTy.
Import ListNotations.

(** The adapter consumes PolCert's actual module interface. It introduces no
    model of memory, arithmetic, or instruction evaluation. *)
Module PolCertSchedule (I : INSTR).

Record invocation := Invocation {
  operation : I.t;
  arguments : list Z;
  writes : list MemCell;
  reads : list MemCell
}.

Definition run (i : invocation) : I.State.t -> I.State.t -> Prop :=
  I.instr_semantics (operation i) (arguments i) (writes i) (reads i).

Definition bernstein (a b : invocation) : Prop :=
  Forall (fun wc2 => Forall (fun wc1 => cell_neq wc1 wc2) (writes a)) (writes b) /\
  Forall (fun rc2 => Forall (fun wc1 => cell_neq wc1 rc2) (writes a)) (reads b) /\
  Forall (fun wc2 => Forall (fun rc1 => cell_neq rc1 wc2) (reads a)) (writes b).

Definition state_relation_equivalence : Equivalence I.State.eq.
Proof.
  constructor.
  - exact I.State.eq_refl.
  - exact I.State.eq_sym.
  - exact I.State.eq_trans.
Defined.

Definition model : scheduling_model I.State.t invocation.
Proof.
  refine {| schedule_invariant := I.NonAlias;
            state_equivalent := I.State.eq;
            state_equivalence := state_relation_equivalence;
            instruction_run := run;
            independent := bernstein |}.
  - intros i s t INV RUN. unfold run in RUN.
    eapply I.sema_prsv_nonalias; eauto.
  - intros i s t s' EQ RUN. exists t. split.
    + unfold run in *. eapply I.instr_semantics_stable_under_state_eq;
        eauto using I.State.eq_refl.
    + apply I.State.eq_refl.
  - intros a b s t u INV BC HA HB. unfold run in *.
    eapply I.bc_condition_implie_permutbility; eauto.
Defined.

Theorem schedule_correct source target :
  schedule_certificate model source target ->
  forall s t, I.NonAlias s -> schedule_run model source s t ->
  exists t', schedule_run model target s t' /\ I.State.eq t t'.
Proof. apply certified_schedule_preserves. Qed.

Print Assumptions schedule_correct.

End PolCertSchedule.
