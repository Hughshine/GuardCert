From Stdlib Require Import List Bool ZArith Lia Sorting.Sorted Sorting.Permutation Sorting.SetoidList.
From polcert.lib Require Import Misc Linalg LinalgExt ListExt ImpureAlarmConfig.
From polcert.src Require Import Base PolyBase PointWitness ExtractorFrontend PrepareCodegen SelectionSort.
From polcert.polygen Require Import PolIRs Result.
From Vpl Require Import Impure.
From Guard Require Import PolCertExtractorOrder.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

(** Forward extraction preserves the caller's actual parameters and instruction
    semantics. Neither a concrete memory model nor equality of State.eq with
    Leibniz equality is required. *)
Module PolCertExtractorForwardFor (IRs : POLIRS).
Module SourceOrder := PolCertExtractorOrderFor IRs.
Include SourceOrder.
Module ForwardPrepare := PrepareCodegen IRs.

Lemma memory_sequence_ordered_flatten parameters instructions (context : list PL.ident) points :
  length context = length parameters ->
  (forall point, In point points <-> memory_sequence_valid_point parameters instructions point) ->
  NoDup points ->
  exists flattened, PL.flatten_instrs parameters instructions flattened /\ Permutation flattened points.
Proof.
  intros LENGTH MEMBERS NODUP.
  set (ordered := SelectionSort ForwardPrepare.np_ltb ForwardPrepare.np_eqb points).
  destruct (@ForwardPrepare.selection_sort_np_is_correct points ordered eq_refl) as [PERM SORTED].
  assert (ORDERED_MEMBERS : forall point, In point ordered <->
    memory_sequence_valid_point parameters instructions point).
  { intro point; rewrite <- MEMBERS; split; eapply Permutation_in;
      [symmetry; exact PERM|exact PERM]. }
  assert (ORDERED_NODUP : NoDup ordered) by (eapply Permutation_NoDup; eassumption).
  assert (ORDERED_NODUPA : NoDupA PL.np_eq ordered).
  { eapply (@ForwardPrepare.source_like_points_imply_NoDupA_np instructions context parameters ordered).
    - intros point MEMBER; apply ORDERED_MEMBERS in MEMBER as [pi [NTH [PREFIX [BELONG INDEX_LENGTH]]]].
      exists (PL.ip_nth point),pi; split; [exact NTH|].
      split; [rewrite LENGTH; exact PREFIX|].
      split; [exact BELONG|].
      split; [reflexivity|rewrite LENGTH; exact INDEX_LENGTH].
    - exact ORDERED_NODUP. }
  exists ordered; split; [|symmetry; exact PERM].
  unfold PL.flatten_instrs; split.
  - intros point MEMBER; apply ORDERED_MEMBERS in MEMBER as [pi [_ [PREFIX _]]]; exact PREFIX.
  - split; [exact ORDERED_MEMBERS|].
    split; [exact ORDERED_NODUP|].
    apply ForwardPrepare.sortedb_np_nodup_implies_sorted_np; assumption.
Qed.

Theorem memory_extracted_stmt_forward st instructions context vars env before after :
  MemoryExtractor.extract_stmt st [] (length env) O [] = Okk instructions ->
  length context = length env ->
  L.loop_semantics st env before after ->
  PL.poly_instance_list_semantics (rev env) (instructions,context,vars) before after.
Proof.
  intros EXTRACT LENGTH RUN.
  set (points := map (memory_extracted_event_point instructions) (indexed_memory_loop_trace O st env)).
  assert (ORDER : StronglySorted memory_sequence_sched_lt points)
    by (unfold points; apply memory_extracted_trace_points_sorted; exact EXTRACT).
  destruct (memory_sequence_strict_order_properties ORDER) as [UNIQUE [SORTED _]].
  destruct (@memory_sequence_ordered_flatten (rev env) instructions context points
    ltac:(rewrite rev_length; exact LENGTH)
    ltac:(intro point; unfold points; apply memory_extracted_trace_coverage_iff; exact EXTRACT) UNIQUE)
    as [flattened [FLAT PERM]].
  eapply PL.PolyPointListSema with (ipl := flattened) (sorted_ipl := points).
  - reflexivity.
  - exact FLAT.
  - exact PERM.
  - exact SORTED.
  - exact (@memory_extracted_trace_execution st instructions env before after EXTRACT RUN).
Qed.

Theorem memory_extractor_forward_at st context vars instructions parameters before after :
  MemoryExtractor.extractor (st,context,vars) = Okk (instructions,context,vars) ->
  length parameters = length context ->
  L.loop_semantics st (rev parameters) before after ->
  PL.poly_instance_list_semantics parameters (instructions,context,vars) before after.
Proof.
  intros EXTRACT LENGTH RUN.
  apply MemoryExtractor.extractor_success_inv in EXTRACT as [pis [EXTRACT [_ PROGRAM]]].
  inversion PROGRAM; subst pis; clear PROGRAM.
  assert (EXTRACT' : MemoryExtractor.extract_stmt st [] (length (rev parameters)) O [] = Okk instructions).
  { rewrite length_rev,LENGTH; exact EXTRACT. }
  pose proof (@memory_extracted_stmt_forward st instructions context vars (rev parameters) before after
    EXTRACT' ltac:(rewrite length_rev; symmetry; exact LENGTH) RUN) as POLY.
  rewrite rev_involutive in POLY; exact POLY.
Qed.

(** Sorting domain rows is a data normalization for the final loop validator.
    It changes neither the domain, the execution order, nor an instruction. *)
Definition memory_constraint_key (row : list Z * Z) := snd row :: fst row.
Definition memory_constraint_lt first second :=
  match lex_compare (memory_constraint_key first) (memory_constraint_key second) with Lt => true | _ => false end.
Definition memory_constraint_eq first second :=
  match lex_compare (memory_constraint_key first) (memory_constraint_key second) with Eq => true | _ => false end.
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
Lemma memory_normalized_flatten parameters instructions points :
  PL.flatten_instrs parameters (memory_normalized_instructions instructions) points <->
  PL.flatten_instrs parameters instructions points.
Proof.
  change (((forall point, In point points -> firstn (length parameters) (PL.ip_index point)=parameters) /\
    (forall point, In point points <-> memory_sequence_valid_point parameters (memory_normalized_instructions instructions) point) /\
    NoDup points /\ Sorted PL.np_lt points) <->
    ((forall point, In point points -> firstn (length parameters) (PL.ip_index point)=parameters) /\
    (forall point, In point points <-> memory_sequence_valid_point parameters instructions point) /\
    NoDup points /\ Sorted PL.np_lt points)).
  split; intros [PREFIX [MEMBERS REST]].
  - split; [exact PREFIX|split; [|exact REST]].
    intro point; rewrite MEMBERS,memory_normalized_point_valid; reflexivity.
  - split; [exact PREFIX|split; [|exact REST]].
    intro point; rewrite MEMBERS,memory_normalized_point_valid; reflexivity.
Qed.
Theorem memory_domain_normalization_execution parameters instructions context vars initial final :
  PL.poly_instance_list_semantics parameters (instructions,context,vars) initial final <->
  PL.poly_instance_list_semantics parameters (memory_normalized_instructions instructions,context,vars) initial final.
Proof.
  split; intro RUN;
    inversion RUN as [params program pis ctx vs first last flattened ordered PROGRAM FLAT PERM SORTED EXEC]; subst;
    inversion PROGRAM; subst; clear PROGRAM;
    eapply PL.PolyPointListSema with (ipl := flattened) (sorted_ipl := ordered);
    try reflexivity; try eassumption.
  - apply (proj2 (@memory_normalized_flatten _ _ _)); exact FLAT.
  - apply (proj1 (@memory_normalized_flatten _ _ _)); exact FLAT.
Qed.
Definition memory_normalize_poly_program (program : PL.t) :=
  let '(instructions,context,vars) := program in (memory_normalized_instructions instructions,context,vars).

Print Assumptions memory_sequence_ordered_flatten.
Print Assumptions memory_extracted_stmt_forward.
Print Assumptions memory_extractor_forward_at.
Print Assumptions memory_domain_normalization_execution.
End PolCertExtractorForwardFor.
