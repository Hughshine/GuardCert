From Stdlib Require Import List Bool.
From compcert.lib Require Import Maps Coqlib.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Ctypes Clight.
From Guard Require Import ClightGuard ClightTempFootprint.
Import ListNotations.
Set Implicit Arguments.

(** Facts about actual Clight function environments. No memory definedness or
    array permissions are inferred from declarations. *)
Definition locals_avoid (globals : list ident) (locals : env) :=
  forall identifier, In identifier globals -> locals ! identifier=None.
Definition function_avoids globals f :=
  forall identifier, In identifier globals ->
    ~ In identifier (var_names (fn_params f ++ fn_vars f)).
Definition fundef_avoids globals fd :=
  match fd with Internal f => function_avoids globals f | External _ _ _ _ => True end.
Definition program_avoids globals p := forall name fd,
  In (name,Gfun fd) (prog_defs p) -> fundef_avoids globals fd.
Definition function_avoids_check globals f := forallb
  (fun identifier => negb (existsb (Pos.eqb identifier) (var_names (fn_params f ++ fn_vars f)))) globals.
Definition program_avoids_check globals (p : program) := forallb
  (fun definition => match snd definition with
    | Gfun (Internal f) => function_avoids_check globals f | _ => true end) (prog_defs p).
Lemma function_avoids_check_sound globals f : function_avoids_check globals f=true -> function_avoids globals f.
Proof.
  intros CHECK identifier MEMBER USED; unfold function_avoids_check in CHECK.
  apply forallb_forall with (x:=identifier) in CHECK; [|exact MEMBER].
  apply negb_true_iff in CHECK; assert (FOUND : existsb (Pos.eqb identifier)
    (var_names (fn_params f++fn_vars f))=true).
  { apply existsb_exists; exists identifier; split; [exact USED|apply Pos.eqb_refl]. }
  congruence.
Qed.
Lemma program_avoids_check_sound globals p : program_avoids_check globals p=true -> program_avoids globals p.
Proof.
  intros CHECK name fd MEMBER; unfold program_avoids_check in CHECK.
  apply forallb_forall with (x:=(name,Gfun fd)) in CHECK; [|exact MEMBER].
  destruct fd; [apply function_avoids_check_sound; exact CHECK|exact I].
Qed.
Lemma allocation_avoids ge locals memory variables after final globals :
  alloc_variables ge locals memory variables after final ->
  locals_avoid globals locals ->
  (forall identifier, In identifier globals -> ~ In identifier (var_names variables)) ->
  locals_avoid globals after.
Proof.
  intro ALLOC; induction ALLOC; intros BEFORE DECLS; [exact BEFORE|].
  apply IHALLOC.
  - intros identifier MEMBER; rewrite PTree.gso.
    + apply BEFORE; exact MEMBER.
    + intro SAME; subst identifier; apply (DECLS id MEMBER); cbn; auto.
  - intros identifier MEMBER USED; apply (DECLS identifier MEMBER); cbn; right; exact USED.
Qed.
Lemma function_entry_avoids temps ge f args memory locals values final globals :
  function_avoids globals f -> adapter_entry temps ge f args memory locals values final ->
  locals_avoid globals locals.
Proof.
  intros DECLS ENTRY; unfold adapter_entry in ENTRY; destruct temps; inversion ENTRY; subst.
  - eapply allocation_avoids; [eassumption|intros identifier MEMBER; apply PTree.gempty|].
    intros identifier MEMBER USED; apply (DECLS identifier MEMBER).
    unfold var_names; rewrite map_app; apply in_or_app; right; exact USED.
  - eapply allocation_avoids; [eassumption|intros identifier MEMBER; apply PTree.gempty|exact DECLS].
Qed.
Lemma program_avoids_lookup globals p value fd : program_avoids globals p ->
  Genv.find_funct (globalenv p) value=Some fd -> fundef_avoids globals fd.
Proof. intros PROGRAM LOOKUP; apply Genv.find_funct_inversion in LOOKUP as [name MEMBER]; eauto. Qed.
Lemma program_avoids_ptr_lookup globals p block fd : program_avoids globals p ->
  Genv.find_funct_ptr (globalenv p) block=Some fd -> fundef_avoids globals fd.
Proof. intros PROGRAM LOOKUP; apply Genv.find_funct_ptr_inversion in LOOKUP as [name MEMBER]; eauto. Qed.

Fixpoint continuation_avoids globals k : Prop :=
  match k with
  | Kstop => True
  | Kseq _ k | Kloop1 _ _ k | Kloop2 _ _ k | Kswitch k => continuation_avoids globals k
  | Kcall _ _ locals _ k => locals_avoid globals locals /\ continuation_avoids globals k
  end.
Definition state_avoids globals source :=
  match source with
  | State _ _ k locals _ _ => locals_avoid globals locals /\ continuation_avoids globals k
  | Callstate fd _ k _ => fundef_avoids globals fd /\ continuation_avoids globals k
  | Returnstate _ k _ => continuation_avoids globals k
  end.
Lemma call_cont_avoids globals k : continuation_avoids globals k -> continuation_avoids globals (call_cont k).
Proof. induction k; cbn; intuition. Qed.
Lemma find_label_avoids :
  (forall source globals label k found next,
    continuation_avoids globals k -> find_label label source k=Some (found,next) -> continuation_avoids globals next) /\
  (forall cases globals label k found next,
    continuation_avoids globals k -> find_label_ls label cases k=Some (found,next) -> continuation_avoids globals next).
Proof.
  apply ClightGuard.statement_cases_ind; intros; cbn in *; try discriminate;
    try solve [eauto].
  - destruct (find_label label s (Kseq s0 k)) as [[code rest]|] eqn:LEFT.
    + inversion H2; subst; eapply (H globals label (Kseq s0 k)); [exact H1|exact LEFT].
    + eapply H0; eauto.
  - destruct (find_label label s k) as [[code rest]|] eqn:LEFT.
    + inversion H2; subst; eapply H; eauto.
    + eapply H0; eauto.
  - destruct (find_label label s (Kloop1 s s0 k)) as [[code rest]|] eqn:LEFT.
    + inversion H2; subst; eapply (H globals label (Kloop1 s s0 k)); [exact H1|exact LEFT].
    + eapply (H0 globals label (Kloop2 s s0 k)); eauto.
  - eapply (H globals label (Kswitch k)); eauto.
  - destruct (ident_eq label l).
    + inversion H1; subst; exact H0.
    + eapply H; eauto.
  - destruct (find_label label s (Kseq (seq_of_labeled_statement l) k)) as [[code rest]|] eqn:LEFT.
    + inversion H2; subst; eapply (H globals label (Kseq (seq_of_labeled_statement l) k)); [exact H1|exact LEFT].
    + eapply H0; eauto.
Qed.
Theorem step_preserves_global_scope globals p temps before events after :
  program_avoids globals p -> state_avoids globals before ->
  adapter_step temps (globalenv p) before events after -> state_avoids globals after.
Proof.
  intros PROGRAM BEFORE STEP; inversion STEP; subst; cbn [state_avoids continuation_avoids] in BEFORE |- *;
    try solve [intuition eauto using call_cont_avoids].
  - split; [eapply program_avoids_lookup; eauto|exact BEFORE].
  - destruct BEFORE as [LOCAL CONT]; split; [exact LOCAL|].
    eapply (proj1 find_label_avoids); [apply call_cont_avoids; exact CONT|eassumption].
  - destruct BEFORE as [FUNCTION CONT]; split; [eapply function_entry_avoids; eauto|exact CONT].
Qed.
Lemma initial_global_scope globals p source : program_avoids globals p ->
  initial_state p source -> state_avoids globals source.
Proof.
  intros PROGRAM INIT; inversion INIT; subst; cbn [state_avoids continuation_avoids].
  split; [eapply program_avoids_ptr_lookup; eauto|exact I].
Qed.

Print Assumptions program_avoids_check_sound.
Print Assumptions function_entry_avoids.
Print Assumptions step_preserves_global_scope.
Print Assumptions initial_global_scope.
