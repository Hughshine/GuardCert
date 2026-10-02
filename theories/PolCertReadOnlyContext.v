From Stdlib Require Import List ZArith.
From polcert.polygen Require Import StateTy InstrTy.
From polcert.polygen Require Import IterSemantics.
From polcert.lib Require Import ImpureAlarmConfig.
From polcert.src Require Import PolyBase.
Set Implicit Arguments.

Module Type CONTEXT_COMPATIBILITY (I : INSTR).
  Parameter compatible : list (I.ident * I.Ty.t) -> I.State.t -> Prop.
End CONTEXT_COMPATIBILITY.

(** Read-only semantic context is separate from the physical instruction
    state. This instance changes InitEnv explicitly; it does not claim that
    underlying scalar variables occupy memory or alter their instruction
    execution. Every instruction keeps the context snapshot. *)
Module ReadOnlyContext (I : INSTR) (C : CONTEXT_COMPATIBILITY I) <: INSTR.
Module State <: STATE.
  Definition t := ((I.ident -> option Z) * I.State.t)%type.
  Definition non_alias (s : t) := I.State.non_alias (snd s).
  Definition eq (first second : t) : Prop :=
    (forall id, fst first id = fst second id) /\ I.State.eq (snd first) (snd second).
  Lemma eq_refl s : eq s s.
  Proof. split; [reflexivity | apply I.State.eq_refl]. Qed.
  Lemma eq_sym first second : eq first second -> eq second first.
  Proof. intros [CONTEXT MEMORY]; split; [intro id; symmetry; apply CONTEXT | apply I.State.eq_sym; exact MEMORY]. Qed.
  Lemma eq_trans first middle final : eq first middle -> eq middle final -> eq first final.
  Proof.
    intros [A M] [B N]; split.
    - intro id; rewrite A; apply B.
    - eapply I.State.eq_trans; eauto.
  Qed.
  Definition dummy_state : t := (fun _ => None, I.State.dummy_state).
End State.
Module Ty := I.Ty.
Module IterSem := IterSem State.
Module IterSemImpure := IterSem.IterImpureSemantics CoreAlarmed.

Definition t := I.t.
Definition dummy_instr := I.dummy_instr.
Definition ident := I.ident.
Definition ident_eqb := I.ident_eqb.
Definition ident_eqb_eq := I.ident_eqb_eq.
Definition ident_to_varname := I.ident_to_varname.
Definition ident_to_openscop_ident := I.ident_to_openscop_ident.
Definition openscop_ident_to_ident := I.openscop_ident_to_ident.
Definition varname_to_ident := I.varname_to_ident.
Definition bind_ident_varname := I.bind_ident_varname.
Definition iterator_to_varname := I.iterator_to_varname.

Definition instr_semantics i parameters writes reads (source target : State.t) : Prop :=
  (forall id, fst target id = fst source id) /\
    I.instr_semantics i parameters writes reads (snd source) (snd target).

Lemma instr_semantics_stable_under_state_eq i parameters writes reads
  first second first' second' :
  State.eq first first' -> State.eq second second' ->
  instr_semantics i parameters writes reads first second ->
  instr_semantics i parameters writes reads first' second'.
Proof.
  intros [CTX1 MEM1] [CTX2 MEM2] [CONTEXT RUN]; split.
  - intro id; rewrite <- CTX2, CONTEXT, CTX1; reflexivity.
  - eapply I.instr_semantics_stable_under_state_eq; eauto.
Qed.

Definition eqb := I.eqb.
Definition eqb_eq := I.eqb_eq.
Definition NonAlias (s : State.t) := I.NonAlias (snd s).
Definition InitEnv (names : list ident) (values : list Z) (s : State.t) :=
  Forall2 (fun id value => fst s id = Some value) names values.
Definition Compat variables (s : State.t) := C.compatible variables (snd s).

Lemma init_env_samelen names values s : InitEnv names values s -> length names = length values.
Proof. intro INIT; induction INIT; simpl; congruence. Qed.

Definition to_openscop := I.to_openscop.
Definition waccess := I.waccess.
Definition raccess := I.raccess.
Definition valid_access_function wl rl i := forall parameters source target writes reads,
  instr_semantics i parameters writes reads source target ->
  valid_access_cells parameters writes wl /\ valid_access_cells parameters reads rl.
Definition check_never_written := I.check_never_written.
Definition access_function_checker := I.access_function_checker.

Lemma access_function_checker_correct wl rl i :
  access_function_checker wl rl i = true -> valid_access_function wl rl i.
Proof.
  intros CHECK parameters source target writes reads [_ RUN].
  exact (I.access_function_checker_correct wl rl i CHECK _ _ _ _ _ RUN).
Qed.

Lemma sema_prsv_nonalias i parameters writes reads first second :
  NonAlias first -> instr_semantics i parameters writes reads first second -> NonAlias second.
Proof. intros ALIAS [_ RUN]; eapply I.sema_prsv_nonalias; eauto. Qed.

Lemma bc_condition_implie_permutbility i1 p1 wcs1 rcs1 first middle final i2 p2 wcs2 rcs2 :
  NonAlias first ->
  (instr_semantics i1 p1 wcs1 rcs1 first middle /\
   instr_semantics i2 p2 wcs2 rcs2 middle final) ->
  (Forall (fun wc2 => Forall (fun wc1 => cell_neq wc1 wc2) wcs1) wcs2) /\
  (Forall (fun rc2 => Forall (fun wc1 => cell_neq wc1 rc2) wcs1) rcs2) /\
  (Forall (fun wc2 => Forall (fun rc1 => cell_neq rc1 wc2) rcs1) wcs2) ->
  exists middle' final', instr_semantics i2 p2 wcs2 rcs2 first middle' /\
    instr_semantics i1 p1 wcs1 rcs1 middle' final' /\ State.eq final final'.
Proof.
  intros ALIAS [[CTX1 RUN1] [CTX2 RUN2]] BC.
  destruct (@I.bc_condition_implie_permutbility i1 p1 wcs1 rcs1
    (snd first) (snd middle) (snd final) i2 p2 wcs2 rcs2 ALIAS (conj RUN1 RUN2) BC)
    as [middle_memory [final_memory [RUN2' [RUN1' EQ]]]].
  exists (fst first, middle_memory), (fst first, final_memory).
  split; [split; [reflexivity | exact RUN2'] |].
  split; [split; [reflexivity | exact RUN1'] |].
  split; [intro id; cbn; rewrite CTX2, CTX1; reflexivity | exact EQ].
Qed.

Lemma context_preserved i parameters writes reads first second :
  instr_semantics i parameters writes reads first second ->
  forall id, fst first id = fst second id.
Proof. intros [CONTEXT RUN] id; symmetry; apply CONTEXT. Qed.

Lemma init_env_unique names first second s : InitEnv names first s -> InitEnv names second s -> first = second.
Proof.
  intros FIRST; revert second; induction FIRST; intros second SECOND; inversion SECOND; subst; auto.
  f_equal; [congruence | eauto].
Qed.

Lemma init_env_preserved names values i parameters writes reads first second :
  InitEnv names values first -> instr_semantics i parameters writes reads first second ->
  InitEnv names values second.
Proof.
  intros INIT [CONTEXT RUN]; induction INIT; constructor; auto. rewrite CONTEXT; assumption.
Qed.

Lemma compatibility_projection vars s : Compat vars s <-> C.compatible vars (snd s).
Proof. reflexivity. Qed.

Print Assumptions bc_condition_implie_permutbility.
Print Assumptions init_env_unique.
End ReadOnlyContext.
