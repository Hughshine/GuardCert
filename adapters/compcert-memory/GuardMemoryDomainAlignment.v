From Stdlib Require Import List Bool ZArith.
From polcert.lib Require Import Linalg ImpureAlarmConfig.
From polcert.polygen Require Import PolyTest.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryPolyhedral GuardMemoryPolyhedralRectangles
  GuardMemorySequencePolyhedral GuardMemoryPointIsomorphism.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

(** Inclusion is checked by refuting each violated integer inequality. Only
    the existing emptiness certificate oracle is used. *)
Fixpoint memory_check_domain_inclusion source target :=
  match target with
  | [] => pure true
  | row::rest =>
    BIND empty <- isBottom (neg_constraint row::source) -;
    if empty then memory_check_domain_inclusion source rest else pure false
  end.
Lemma memory_check_domain_inclusion_correct source target :
  mayReturn (memory_check_domain_inclusion source target) true ->
  forall index, in_poly index source = true -> in_poly index target = true.
Proof.
  revert source; induction target as [|row rest IH]; intros source CHECK index SOURCE; [reflexivity|].
  cbn in CHECK; bind_imp_destruct CHECK empty EMPTY.
  destruct empty; [|apply mayReturn_pure in CHECK; discriminate].
  assert (ROW : satisfies_constraint index row = true).
  { pose proof (@isBottom_correct_1 (neg_constraint row::source) true EMPTY index) as BOTTOM.
    change (satisfies_constraint index (neg_constraint row) && in_poly index source = false) in BOTTOM.
    rewrite neg_constraint_correct,SOURCE,andb_true_r in BOTTOM.
    destruct (satisfies_constraint index row); [reflexivity|discriminate]. }
  change (satisfies_constraint index row && in_poly index rest = true).
  rewrite ROW; apply IH with (source := source); assumption.
Qed.
Definition memory_check_domain_equivalence first second :=
  if list_eq_dec affine_term_eq_dec first second then pure true else
  BIND forward <- memory_check_domain_inclusion first second -;
  BIND backward <- memory_check_domain_inclusion second first -;
  pure (forward && backward).
Lemma memory_check_domain_equivalence_correct first second :
  mayReturn (memory_check_domain_equivalence first second) true ->
  forall index, in_poly index first = in_poly index second.
Proof.
  unfold memory_check_domain_equivalence; destruct (list_eq_dec affine_term_eq_dec first second) as [SAME|DIFFERENT].
  - subst second; intros; reflexivity.
  - intro CHECK.
  bind_imp_destruct CHECK forward FORWARD; bind_imp_destruct CHECK backward BACKWARD.
  apply mayReturn_pure in CHECK; apply andb_true_iff in CHECK as [F B]; subst forward backward.
  intro index; apply eq_true_iff_eq; split;
    apply memory_check_domain_inclusion_correct; assumption.
Qed.
Definition memory_replace_domain rows (pi : PL.PolyInstr) : PL.PolyInstr :=
  {| PL.pi_depth := PL.pi_depth pi; PL.pi_instr := PL.pi_instr pi; PL.pi_poly := rows;
     PL.pi_schedule := PL.pi_schedule pi; PL.pi_point_witness := PL.pi_point_witness pi;
     PL.pi_transformation := PL.pi_transformation pi; PL.pi_access_transformation := PL.pi_access_transformation pi;
     PL.pi_waccess := PL.pi_waccess pi; PL.pi_raccess := PL.pi_raccess pi |}.
Fixpoint memory_align_domains reference candidate : CoreAlarmed.Base.imp (option (list PL.PolyInstr)) :=
  match reference,candidate with
  | [],[] => pure (Some [])
  | source::sources,target::targets =>
    BIND same <- memory_check_domain_equivalence (PL.pi_poly source) (PL.pi_poly target) -;
    if same then
      BIND aligned <- memory_align_domains sources targets -;
      pure (match aligned with Some rest => Some (memory_replace_domain (PL.pi_poly source) target::rest)
                              | None => None end)
    else pure None
  | _,_ => pure None end.
Definition memory_domain_representation_equal first second :=
  (forall point, PL.belongs_to point first <-> PL.belongs_to point second) /\ PL.pi_depth first = PL.pi_depth second.
Lemma memory_replace_domain_equivalent rows pi :
  (forall index, in_poly index rows = in_poly index (PL.pi_poly pi)) ->
  memory_domain_representation_equal pi (memory_replace_domain rows pi).
Proof.
  intro DOMAINS; split; [|reflexivity].
  intro point; unfold PL.belongs_to; cbn [memory_replace_domain PL.pi_poly PL.pi_schedule
    PL.pi_transformation PL.pi_access_transformation PL.pi_instr PL.pi_depth PL.pi_point_witness].
  rewrite DOMAINS; reflexivity.
Qed.
Lemma memory_align_domains_correct reference candidate aligned :
  mayReturn (memory_align_domains reference candidate) (Some aligned) ->
  Forall2 memory_domain_representation_equal candidate aligned.
Proof.
  revert candidate aligned; induction reference; intros candidate aligned CHECK;
    destruct candidate; cbn in CHECK.
  - apply mayReturn_pure in CHECK; inversion CHECK; constructor.
  - apply mayReturn_pure in CHECK; discriminate.
  - apply mayReturn_pure in CHECK; discriminate.
  - bind_imp_destruct CHECK same SAME; destruct same;
      [|apply mayReturn_pure in CHECK; discriminate].
    bind_imp_destruct CHECK rest REST; apply mayReturn_pure in CHECK.
    destruct rest; [|discriminate]; inversion CHECK; subst aligned; constructor.
    + apply memory_replace_domain_equivalent; eapply memory_check_domain_equivalence_correct; exact SAME.
    + apply IHreference; exact REST.
Qed.
Lemma memory_domain_representation_valid parameters source target :
  Forall2 memory_domain_representation_equal source target ->
  forall point, memory_sequence_valid_point parameters source point <-> memory_sequence_valid_point parameters target point.
Proof.
  intro REPRESENTATIONS; induction REPRESENTATIONS as [|first second source target EQUAL REST IH]; intro point.
  - reflexivity.
  - unfold memory_sequence_valid_point in IH |- *.
    split; intros [pi [NTH [PREFIX [BELONG LENGTH]]]];
      destruct (PL.ILSema.ip_nth point) eqn:SITE.
    + cbn in NTH; inversion NTH; subst pi.
      exists second; split; [reflexivity|]; split; [exact PREFIX|].
      destruct EQUAL as [BOTH DEPTH]; split; [apply BOTH; exact BELONG|rewrite <- DEPTH; exact LENGTH].
    + assert (VALID : exists pi, nth_error source n = Some pi /\
        firstn (length parameters) (PL.ILSema.ip_index point) = parameters /\
        PL.belongs_to point pi /\ length (PL.ILSema.ip_index point) = (length parameters+PL.pi_depth pi)%nat).
      { exists pi; cbn in NTH; auto. }
      (* The static site changes only in this local list induction. *)
      set (tail_point := {| PL.ILSema.ip_nth := n; PL.ILSema.ip_index := PL.ILSema.ip_index point;
        PL.ILSema.ip_transformation := PL.ILSema.ip_transformation point;
        PL.ILSema.ip_time_stamp := PL.ILSema.ip_time_stamp point;
        PL.ILSema.ip_instruction := PL.ILSema.ip_instruction point; PL.ILSema.ip_depth := PL.ILSema.ip_depth point |}).
      assert (TAIL : memory_sequence_valid_point parameters source tail_point) by exact VALID.
      apply (proj1 (IH tail_point)) in TAIL as [other [OTHER [PARAMS [BODY SIZE]]]].
      exists other; split; [cbn; exact OTHER|]; auto.
    + cbn in NTH; inversion NTH; subst pi.
      exists first; split; [reflexivity|]; split; [exact PREFIX|].
      destruct EQUAL as [BOTH DEPTH]; split; [apply BOTH; exact BELONG|rewrite DEPTH; exact LENGTH].
    + set (tail_point := {| PL.ILSema.ip_nth := n; PL.ILSema.ip_index := PL.ILSema.ip_index point;
        PL.ILSema.ip_transformation := PL.ILSema.ip_transformation point;
        PL.ILSema.ip_time_stamp := PL.ILSema.ip_time_stamp point;
        PL.ILSema.ip_instruction := PL.ILSema.ip_instruction point; PL.ILSema.ip_depth := PL.ILSema.ip_depth point |}).
      assert (TAIL : memory_sequence_valid_point parameters target tail_point).
      { exists pi; cbn in NTH; auto. }
      apply (proj2 (IH tail_point)) in TAIL as [other [OTHER [PARAMS [BODY SIZE]]]].
      exists other; split; [cbn; exact OTHER|]; auto.
Qed.
Definition memory_domain_alignment_isomorphism parameters source target
  (REPRESENTATIONS : Forall2 memory_domain_representation_equal source target) :
  memory_point_isomorphism parameters source target.
Proof.
  refine {| point_forward := fun point => point; point_backward := fun point => point |};
    intros; try reflexivity; try assumption;
    apply (memory_domain_representation_valid parameters REPRESENTATIONS); assumption.
Defined.
Theorem memory_aligned_domains_execution parameters reference candidate aligned context vars initial final :
  mayReturn (memory_align_domains reference candidate) (Some aligned) ->
  (PL.poly_instance_list_semantics parameters (candidate,context,vars) initial final <->
   PL.poly_instance_list_semantics parameters (aligned,context,vars) initial final).
Proof.
  intro CHECK; apply memory_point_isomorphism_execution; apply memory_domain_alignment_isomorphism.
  eapply memory_align_domains_correct; exact CHECK.
Qed.
Print Assumptions memory_check_domain_equivalence_correct.
Print Assumptions memory_aligned_domains_execution.
