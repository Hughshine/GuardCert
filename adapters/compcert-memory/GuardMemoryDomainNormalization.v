From Stdlib Require Import List Bool ZArith Sorting.Permutation.
From polcert.lib Require Import Linalg.
From polcert.src Require Import SelectionSort Base.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryPolyhedral GuardMemoryPolyhedralRectangles
  GuardMemorySequencePolyhedral GuardMemoryPointIsomorphism.
Import ListNotations.
Set Implicit Arguments.

Definition memory_constraint_key (row : list Z * Z) := snd row :: fst row.
Definition memory_constraint_lt first second :=
  match lex_compare (memory_constraint_key first) (memory_constraint_key second) with Lt => true | _ => false end.
Definition memory_constraint_eq first second := if affine_term_eq_dec first second then true else false.
Definition memory_sorted_domain rows := SelectionSort memory_constraint_lt memory_constraint_eq rows.
Lemma memory_sorted_domain_permutation rows : Permutation rows (memory_sorted_domain rows).
Proof. apply selection_sort_perm. Qed.
Lemma memory_domain_permutation_at index first second :
  Permutation first second -> in_poly index first = in_poly index second.
Proof.
  intro PERM; unfold in_poly.
  apply eq_true_iff_eq; rewrite !forallb_forall.
  split; intros ALL row MEMBER; apply ALL.
  - eapply Permutation_in; [apply Permutation_sym; exact PERM|exact MEMBER].
  - eapply Permutation_in; [exact PERM|exact MEMBER].
Qed.
Definition memory_normalized_instruction (pi : PL.PolyInstr) : PL.PolyInstr :=
  {| PL.pi_depth := PL.pi_depth pi; PL.pi_instr := PL.pi_instr pi;
     PL.pi_poly := memory_sorted_domain (PL.pi_poly pi);
     PL.pi_schedule := PL.pi_schedule pi; PL.pi_point_witness := PL.pi_point_witness pi;
     PL.pi_transformation := PL.pi_transformation pi; PL.pi_access_transformation := PL.pi_access_transformation pi;
     PL.pi_waccess := PL.pi_waccess pi; PL.pi_raccess := PL.pi_raccess pi |}.
Definition memory_normalized_instructions := map memory_normalized_instruction.
Lemma memory_normalized_belongs point pi :
  PL.belongs_to point (memory_normalized_instruction pi) <-> PL.belongs_to point pi.
Proof.
  unfold PL.belongs_to; cbn [memory_normalized_instruction PL.pi_poly PL.pi_schedule
    PL.pi_transformation PL.pi_access_transformation PL.pi_instr PL.pi_depth PL.pi_point_witness].
  rewrite <- (memory_domain_permutation_at (PL.ILSema.ip_index point) (memory_sorted_domain_permutation (PL.pi_poly pi))).
  reflexivity.
Qed.
Lemma memory_normalized_point_valid parameters instructions point :
  memory_sequence_valid_point parameters (memory_normalized_instructions instructions) point <->
  memory_sequence_valid_point parameters instructions point.
Proof.
  unfold memory_sequence_valid_point,memory_normalized_instructions; split.
  - intros [normalized [NTH [PREFIX [BELONG LENGTH]]]].
    rewrite nth_error_map in NTH.
    destruct (nth_error instructions (PL.ILSema.ip_nth point)) as [pi|] eqn:ORIGINAL; [|discriminate].
    inversion NTH; subst normalized.
    exists pi; split; [reflexivity|]; split; [exact PREFIX|]; split.
    + apply memory_normalized_belongs; exact BELONG.
    + exact LENGTH.
  - intros [pi [NTH [PREFIX [BELONG LENGTH]]]].
    exists (memory_normalized_instruction pi); split.
    + rewrite nth_error_map,NTH; reflexivity.
    + split; [exact PREFIX|]; split; [apply memory_normalized_belongs; exact BELONG|exact LENGTH].
Qed.
Definition memory_domain_normalization_isomorphism parameters instructions :
  memory_point_isomorphism parameters instructions (memory_normalized_instructions instructions).
Proof.
  refine {| point_forward := fun point => point; point_backward := fun point => point |};
    intros; try reflexivity; try assumption; apply memory_normalized_point_valid; assumption.
Defined.
Theorem memory_domain_normalization_execution parameters instructions context vars initial final :
  PL.poly_instance_list_semantics parameters (instructions,context,vars) initial final <->
  PL.poly_instance_list_semantics parameters (memory_normalized_instructions instructions,context,vars) initial final.
Proof. apply memory_point_isomorphism_execution; apply memory_domain_normalization_isomorphism. Qed.
Print Assumptions memory_domain_normalization_execution.
