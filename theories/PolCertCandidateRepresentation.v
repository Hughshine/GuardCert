From Stdlib Require Import List Bool ZArith Lia Sorting.Sorted Sorting.Permutation.
From polcert.lib Require Import Linalg ImpureAlarmConfig.
From polcert.src Require Import PointWitness.
From polcert.polygen Require Import PolIRs PolyTest Result.
From Vpl Require Import Impure.
From Guard Require Import PolCertExtractorForward.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Representation witnesses preserve points and their actual instructions.
    Domain equivalence uses the existing checked emptiness certificates. *)
Module PolCertCandidateRepresentationFor (IRs : POLIRS).
Module RepresentationForward := PolCertExtractorForwardFor IRs.
Include RepresentationForward.
Record memory_point_isomorphism parameters source target := MemoryPointIsomorphism {
  point_forward : PL.InstrPoint -> PL.InstrPoint;
  point_backward : PL.InstrPoint -> PL.InstrPoint;
  point_forward_valid : forall point, memory_sequence_valid_point parameters source point ->
    memory_sequence_valid_point parameters target (point_forward point);
  point_backward_valid : forall point, memory_sequence_valid_point parameters target point ->
    memory_sequence_valid_point parameters source (point_backward point);
  point_forward_inverse : forall point, memory_sequence_valid_point parameters source point ->
    point_backward (point_forward point) = point;
  point_backward_inverse : forall point, memory_sequence_valid_point parameters target point ->
    point_forward (point_backward point) = point;
  point_forward_time : forall point, memory_sequence_valid_point parameters source point ->
    PL.ILSema.ip_time_stamp (point_forward point) = PL.ILSema.ip_time_stamp point;
  point_backward_time : forall point, memory_sequence_valid_point parameters target point ->
    PL.ILSema.ip_time_stamp (point_backward point) = PL.ILSema.ip_time_stamp point;
  point_forward_execution : forall point initial final,
    memory_sequence_valid_point parameters source point ->
    PL.instr_point_sema point initial final -> PL.instr_point_sema (point_forward point) initial final;
  point_backward_execution : forall point initial final,
    memory_sequence_valid_point parameters target point ->
    PL.instr_point_sema point initial final -> PL.instr_point_sema (point_backward point) initial final
}.

Lemma memory_valid_map_nodup {A B} (valid : A -> Prop) (f : A -> B) (g : B -> A) points :
  (forall point, valid point -> g (f point) = point) ->
  (forall point, In point points -> valid point) ->
  NoDup points -> NoDup (map f points).
Proof.
  intros INVERSE VALID UNIQUE; induction UNIQUE; cbn; constructor.
  - intro MEMBER; apply in_map_iff in MEMBER as [other [SAME MEMBER]].
    apply H; assert (EQ : other = x).
    { rewrite <- (INVERSE other (VALID other (or_intror MEMBER))),
        <- (INVERSE x (VALID x (or_introl eq_refl))); congruence. }
    subst other; exact MEMBER.
  - apply IHUNIQUE; intros point MEMBER; apply VALID; right; exact MEMBER.
Qed.
Lemma memory_sorted_timestamp_map f points :
  (forall point, In point points -> PL.ILSema.ip_time_stamp (f point) = PL.ILSema.ip_time_stamp point) ->
  Sorted PL.instr_point_sched_le points -> Sorted PL.instr_point_sched_le (map f points).
Proof.
  intros TIMES ORDER; induction ORDER; cbn; constructor.
  - apply IHORDER; intros point MEMBER; apply TIMES; right; exact MEMBER.
  - inversion H; subst; constructor.
    unfold PL.instr_point_sched_le,PL.ILSema.instr_point_sched_lt,PL.ILSema.instr_point_sched_eq,
      PL.ILSema.instr_point_sched_ltb,PL.ILSema.instr_point_sched_eqb in *.
    rewrite (TIMES a (or_introl eq_refl)),(TIMES b (or_intror (or_introl eq_refl))); assumption.
Qed.
Lemma memory_point_execution_map f points initial final :
  (forall point before after, In point points ->
    PL.instr_point_sema point before after -> PL.instr_point_sema (f point) before after) ->
  PL.instr_point_list_semantics points initial final ->
  PL.instr_point_list_semantics (map f points) initial final.
Proof.
  intros MAP RUN; induction RUN; cbn.
  - constructor; assumption.
  - econstructor.
    + apply MAP; [left; reflexivity|exact H].
    + apply IHRUN; intros point before after MEMBER; apply MAP; right; exact MEMBER.
Qed.

Theorem memory_point_isomorphism_forward parameters source target context vars initial final
  (iso : memory_point_isomorphism parameters source target) :
  length context = length parameters ->
  PL.poly_instance_list_semantics parameters (source,context,vars) initial final ->
  PL.poly_instance_list_semantics parameters (target,context,vars) initial final.
Proof.
  intros LENGTH RUN; inversion RUN as [params program instructions ctxt variables before after flattened ordered
    PROGRAM FLAT PERM SORTED EXEC]; subst.
  injection PROGRAM as INSTRUCTIONS CONTEXT VARIABLES; subst instructions ctxt variables.
  assert (MEMBERS : forall point, In point ordered <-> memory_sequence_valid_point parameters source point).
  { intro point; unfold memory_sequence_valid_point.
    destruct FLAT as [_ [COVER [_ _]]]; rewrite <- COVER.
    split; eapply Permutation_in; [apply Permutation_sym; exact PERM|exact PERM]. }
  assert (UNIQUE : NoDup ordered).
  { eapply Permutation_NoDup; [exact PERM|exact (proj1 (proj2 (proj2 FLAT)))]. }
  set (mapped := map (point_forward iso) ordered).
  assert (COVER : forall point, In point mapped <-> memory_sequence_valid_point parameters target point).
  { intro point; unfold mapped; split.
    - intro MEMBER; apply in_map_iff in MEMBER as [old [<- MEMBER]].
      apply point_forward_valid; apply MEMBERS; exact MEMBER.
    - intro VALID; apply in_map_iff; exists (point_backward iso point); split.
      + apply point_backward_inverse; exact VALID.
      + apply MEMBERS; apply point_backward_valid; exact VALID. }
  assert (NODUP : NoDup mapped).
  { unfold mapped; eapply memory_valid_map_nodup with (g := point_backward iso).
    - exact (point_forward_inverse iso).
    - intros point MEMBER; apply MEMBERS; exact MEMBER.
    - exact UNIQUE. }
  destruct (@memory_sequence_ordered_flatten parameters target
    context mapped LENGTH COVER NODUP)
    as [canonical [TARGET_FLAT TARGET_PERM]].
  eapply PL.PolyPointListSema with (ipl := canonical) (sorted_ipl := mapped).
  - reflexivity.
  - exact TARGET_FLAT.
  - exact TARGET_PERM.
  - unfold mapped; apply memory_sorted_timestamp_map; [|exact SORTED].
    intros point MEMBER; apply point_forward_time; apply MEMBERS; exact MEMBER.
  - unfold mapped; apply memory_point_execution_map; [|exact EXEC].
    intros point before after MEMBER; apply point_forward_execution; apply MEMBERS; exact MEMBER.
Qed.
Definition memory_point_isomorphism_reverse parameters source target
  (iso : memory_point_isomorphism parameters source target) :
  memory_point_isomorphism parameters target source :=
  {| point_forward := point_backward iso; point_backward := point_forward iso;
     point_forward_valid := point_backward_valid iso; point_backward_valid := point_forward_valid iso;
     point_forward_inverse := point_backward_inverse iso; point_backward_inverse := point_forward_inverse iso;
     point_forward_time := point_backward_time iso; point_backward_time := point_forward_time iso;
     point_forward_execution := point_backward_execution iso; point_backward_execution := point_forward_execution iso |}.
Theorem memory_point_isomorphism_execution parameters source target context vars initial final
  (iso : memory_point_isomorphism parameters source target) :
  length context = length parameters ->
  (PL.poly_instance_list_semantics parameters (source,context,vars) initial final <->
  PL.poly_instance_list_semantics parameters (target,context,vars) initial final).
Proof.
  intro LENGTH; split; intro RUN.
  - exact (@memory_point_isomorphism_forward parameters source target context vars initial final iso LENGTH RUN).
  - exact (@memory_point_isomorphism_forward parameters target source context vars initial final
      (memory_point_isomorphism_reverse iso) LENGTH RUN).
Qed.
Print Assumptions memory_point_isomorphism_execution.

Fixpoint memory_swap_coordinates {A} position (values : list A) :=
  match position,values with
  | O,first::second::rest => second::first::rest
  | S index,first::rest => first::memory_swap_coordinates index rest
  | _,_ => values end.
Lemma memory_swap_coordinates_length {A} position (values : list A) :
  length (memory_swap_coordinates position values) = length values.
Proof. revert values; induction position; intros [|first [|second rest]]; cbn; auto. Qed.
Lemma memory_swap_coordinates_inverse {A} position (values : list A) :
  memory_swap_coordinates position (memory_swap_coordinates position values) = values.
Proof. revert values; induction position; intros [|first [|second rest]]; cbn; congruence. Qed.
Lemma memory_swap_coordinates_prefix {A} position count (values : list A) :
  (count <= position)%nat -> firstn count (memory_swap_coordinates position values) = firstn count values.
Proof.
  revert count values; induction position; intros count values ORDER;
    destruct count; cbn; [reflexivity|lia|reflexivity|].
  destruct values; cbn; [reflexivity|]; f_equal; apply IHposition; lia.
Qed.
Lemma memory_swap_dot_product position first second : length first = length second ->
  dot_product (memory_swap_coordinates position first) (memory_swap_coordinates position second) = dot_product first second.
Proof.
  revert first second; induction position; intros first second LENGTH.
  - destruct first as [|a [|b rest]],second as [|c [|d tail]]; cbn in LENGTH |- *; try lia; try reflexivity; ring.
  - destruct first,second; cbn in LENGTH |- *; try lia; try reflexivity.
    rewrite IHposition by lia; reflexivity.
Qed.
Definition memory_swap_affine position (row : list Z * Z) := (memory_swap_coordinates position (fst row),snd row).
Definition memory_swap_affines position := map (memory_swap_affine position).
Lemma memory_swap_affines_inverse position rows :
  memory_swap_affines position (memory_swap_affines position rows) = rows.
Proof.
  induction rows as [|[coefficients bias] rows IH]; [reflexivity|].
  change ((memory_swap_coordinates position (memory_swap_coordinates position coefficients),bias)::
    memory_swap_affines position (memory_swap_affines position rows) = (coefficients,bias)::rows).
  rewrite memory_swap_coordinates_inverse,IH; reflexivity.
Qed.
Lemma memory_swap_affine_product position rows index :
  Forall (fun row => length (fst row) = length index) rows ->
  affine_product (memory_swap_affines position rows) (memory_swap_coordinates position index) = affine_product rows index.
Proof.
  intro WIDTH; induction WIDTH; [reflexivity|].
  destruct x as [coefficients bias].
  change ((dot_product (memory_swap_coordinates position coefficients) (memory_swap_coordinates position index)+bias)::
    affine_product (memory_swap_affines position l) (memory_swap_coordinates position index) =
    (dot_product coefficients index+bias)::affine_product l index).
  rewrite memory_swap_dot_product by exact H; rewrite IHWIDTH; reflexivity.
Qed.
Lemma memory_swap_domain position rows index :
  Forall (fun row => length (fst row) = length index) rows ->
  in_poly (memory_swap_coordinates position index) (memory_swap_affines position rows) = in_poly index rows.
Proof.
  intro WIDTH; induction WIDTH; [reflexivity|].
  destruct x as [coefficients bias].
  change ((dot_product (memory_swap_coordinates position index) (memory_swap_coordinates position coefficients) <=? bias) &&
    in_poly (memory_swap_coordinates position index) (memory_swap_affines position l) =
    (dot_product index coefficients <=? bias) && in_poly index l).
  rewrite memory_swap_dot_product by (symmetry; exact H); rewrite IHWIDTH; reflexivity.
Qed.
Definition memory_swap_instruction position (pi : PL.PolyInstr) : PL.PolyInstr :=
  {| PL.pi_depth := PL.pi_depth pi; PL.pi_instr := PL.pi_instr pi;
     PL.pi_poly := memory_swap_affines position (PL.pi_poly pi);
     PL.pi_schedule := memory_swap_affines position (PL.pi_schedule pi);
     PL.pi_point_witness := PL.pi_point_witness pi;
     PL.pi_transformation := memory_swap_affines position (PL.pi_transformation pi);
     PL.pi_access_transformation := memory_swap_affines position (PL.pi_access_transformation pi);
     PL.pi_waccess := PL.pi_waccess pi; PL.pi_raccess := PL.pi_raccess pi |}.
Definition memory_swap_instructions position := map (memory_swap_instruction position).
Definition memory_swap_point position (point : PL.InstrPoint) : PL.InstrPoint :=
  {| PL.ILSema.ip_nth := PL.ILSema.ip_nth point;
     PL.ILSema.ip_index := memory_swap_coordinates position (PL.ILSema.ip_index point);
     PL.ILSema.ip_transformation := memory_swap_affines position (PL.ILSema.ip_transformation point);
     PL.ILSema.ip_time_stamp := PL.ILSema.ip_time_stamp point;
     PL.ILSema.ip_instruction := PL.ILSema.ip_instruction point;
     PL.ILSema.ip_depth := PL.ILSema.ip_depth point |}.
Lemma memory_swap_instruction_inverse position pi :
  memory_swap_instruction position (memory_swap_instruction position pi) = pi.
Proof. destruct pi; unfold memory_swap_instruction; cbn; rewrite !memory_swap_affines_inverse; reflexivity. Qed.
Lemma memory_swap_instructions_inverse position instructions :
  memory_swap_instructions position (memory_swap_instructions position instructions) = instructions.
Proof. induction instructions; cbn [memory_swap_instructions map];
  [reflexivity|rewrite memory_swap_instruction_inverse,IHinstructions; reflexivity]. Qed.
Lemma memory_swap_point_inverse position point :
  memory_swap_point position (memory_swap_point position point) = point.
Proof. destruct point; unfold memory_swap_point; cbn; rewrite memory_swap_coordinates_inverse,memory_swap_affines_inverse; reflexivity. Qed.

Definition memory_identity_representation dimension pi :=
  PL.pi_point_witness pi = PSWIdentity (PL.pi_depth pi) /\
  Forall (fun row => length (fst row) = (dimension+PL.pi_depth pi)%nat) (PL.pi_poly pi) /\
  Forall (fun row => length (fst row) = (dimension+PL.pi_depth pi)%nat) (PL.pi_schedule pi) /\
  Forall (fun row => length (fst row) = (dimension+PL.pi_depth pi)%nat) (PL.pi_transformation pi).
Lemma memory_identity_current_transform pi index :
  PL.pi_point_witness pi = PSWIdentity (PL.pi_depth pi) ->
  PL.current_transformation_of pi index = PL.pi_transformation pi.
Proof. intro IDENTITY; unfold PL.current_transformation_of,PL.current_transformation_at;
  rewrite IDENTITY; reflexivity. Qed.

Lemma memory_swap_instruction_representation position dimension pi :
  memory_identity_representation dimension pi ->
  memory_identity_representation dimension (memory_swap_instruction position pi).
Proof.
  intros [IDENTITY [DOMAIN [SCHEDULE TRANSFORM]]]; split; [exact IDENTITY|].
  repeat split; unfold memory_swap_affines; apply Forall_map; eapply Forall_impl;
    [|exact DOMAIN| |exact SCHEDULE| |exact TRANSFORM];
    intros row WIDTH; cbn [memory_swap_affine fst]; rewrite memory_swap_coordinates_length; exact WIDTH.
Qed.

Lemma memory_swap_valid_point position parameters instructions point :
  (length parameters <= position)%nat ->
  Forall (memory_identity_representation (length parameters)) instructions ->
  memory_sequence_valid_point parameters instructions point ->
  memory_sequence_valid_point parameters (memory_swap_instructions position instructions) (memory_swap_point position point).
Proof.
  intros PREFIX REPRESENTATIONS [pi [NTH [PARAMS [BELONG LENGTH]]]].
  assert (REP := proj1 (Forall_forall _ _) REPRESENTATIONS pi ltac:(eapply nth_error_In; exact NTH)).
  destruct REP as [IDENTITY [DOMAIN [SCHEDULE TRANSFORM]]].
  exists (memory_swap_instruction position pi); split.
  - unfold memory_swap_instructions; rewrite nth_error_map; cbn [memory_swap_point PL.ILSema.ip_nth]; rewrite NTH; reflexivity.
  - split.
    + cbn [memory_swap_point PL.ILSema.ip_index]; rewrite memory_swap_coordinates_prefix by exact PREFIX; exact PARAMS.
    + split.
      * unfold PL.belongs_to in BELONG |- *.
        destruct BELONG as [DOMAIN_HOLDS [TF [TIME [INSTRUCTION DEPTH]]]].
        cbn [memory_swap_point memory_swap_instruction PL.ILSema.ip_index PL.ILSema.ip_transformation
          PL.ILSema.ip_time_stamp PL.ILSema.ip_instruction PL.ILSema.ip_depth PL.pi_poly PL.pi_schedule PL.pi_instr PL.pi_depth].
        split.
        -- rewrite memory_swap_domain; [exact DOMAIN_HOLDS|rewrite LENGTH; exact DOMAIN].
        -- split.
           ++ rewrite memory_identity_current_transform in TF by exact IDENTITY.
              rewrite memory_identity_current_transform by exact IDENTITY; rewrite TF; reflexivity.
           ++ split.
              ** rewrite memory_swap_affine_product; [exact TIME|rewrite LENGTH; exact SCHEDULE].
              ** split; assumption.
      * cbn [memory_swap_point memory_swap_instruction PL.ILSema.ip_index PL.pi_depth]; rewrite memory_swap_coordinates_length; exact LENGTH.
Qed.

Lemma memory_swap_point_execution position point initial final :
  Forall (fun row => length (fst row) = length (PL.ILSema.ip_index point)) (PL.ILSema.ip_transformation point) ->
  PL.instr_point_sema point initial final -> PL.instr_point_sema (memory_swap_point position point) initial final.
Proof.
  intros WIDTH RUN; inversion RUN as [writes reads EXEC].
  apply PL.ILSema.ip_sema_intro with (wcs := writes) (rcs := reads).
  cbn [memory_swap_point PL.ILSema.ip_instruction PL.ILSema.ip_transformation PL.ILSema.ip_index].
  rewrite memory_swap_affine_product by exact WIDTH; exact EXEC.
Qed.
Lemma memory_valid_point_transform_width parameters instructions point :
  Forall (memory_identity_representation (length parameters)) instructions ->
  memory_sequence_valid_point parameters instructions point ->
  Forall (fun row => length (fst row) = length (PL.ILSema.ip_index point)) (PL.ILSema.ip_transformation point).
Proof.
  intros REPRESENTATIONS [pi [NTH [PREFIX [BELONG LENGTH]]]].
  pose proof (proj1 (Forall_forall _ _) REPRESENTATIONS pi ltac:(eapply nth_error_In; exact NTH)) as [IDENTITY [_ [_ WIDTH]]].
  unfold PL.belongs_to in BELONG; destruct BELONG as [_ [TRANSFORM _]].
  rewrite TRANSFORM,memory_identity_current_transform by exact IDENTITY; rewrite LENGTH; exact WIDTH.
Qed.

Definition memory_coordinate_swap_isomorphism position parameters instructions
  (PREFIX : (length parameters <= position)%nat)
  (REPRESENTATIONS : Forall (memory_identity_representation (length parameters)) instructions) :
  memory_point_isomorphism parameters instructions (memory_swap_instructions position instructions).
Proof.
  assert (TARGET_REP : Forall (memory_identity_representation (length parameters)) (memory_swap_instructions position instructions)).
  { unfold memory_swap_instructions; apply Forall_map; eapply Forall_impl; [|exact REPRESENTATIONS].
    intros pi REP; apply memory_swap_instruction_representation; exact REP. }
  refine {| point_forward := memory_swap_point position; point_backward := memory_swap_point position |}.
  - intros point VALID; apply memory_swap_valid_point; assumption.
  - intros point VALID.
    pose proof (@memory_swap_valid_point position parameters _ point PREFIX TARGET_REP VALID) as SOURCE.
    rewrite memory_swap_instructions_inverse in SOURCE; exact SOURCE.
  - intros; apply memory_swap_point_inverse.
  - intros; apply memory_swap_point_inverse.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros point initial final VALID RUN; apply memory_swap_point_execution; [|exact RUN].
    exact (@memory_valid_point_transform_width parameters instructions point REPRESENTATIONS VALID).
  - intros point initial final VALID RUN; apply memory_swap_point_execution; [|exact RUN].
    exact (@memory_valid_point_transform_width parameters _ point TARGET_REP VALID).
Defined.
Theorem memory_coordinate_swap_execution position parameters instructions context vars initial final :
  length context = length parameters ->
  (length parameters <= position)%nat ->
  Forall (memory_identity_representation (length parameters)) instructions ->
  (PL.poly_instance_list_semantics parameters (instructions,context,vars) initial final <->
   PL.poly_instance_list_semantics parameters (memory_swap_instructions position instructions,context,vars) initial final).
Proof. intros LENGTH PREFIX REPRESENTATIONS; eapply memory_point_isomorphism_execution;
  [apply memory_coordinate_swap_isomorphism; assumption|exact LENGTH]. Qed.
Print Assumptions memory_coordinate_swap_execution.

Lemma memory_exact_columns_forall dimension rows : exact_listzzs_cols dimension rows ->
  Forall (fun row => length (fst row) = dimension) rows.
Proof. intros WIDTH; apply Forall_forall; intros [coefficients bias] MEMBER;
  exact (WIDTH coefficients bias (coefficients,bias) MEMBER eq_refl). Qed.
Lemma memory_extracted_identity_representation st context vars instructions :
  MemoryExtractor.extractor (st,context,vars) = Okk (instructions,context,vars) ->
  Forall (memory_identity_representation (length context)) instructions.
Proof.
  intro EXTRACT; apply MemoryExtractor.extractor_success_inv in EXTRACT as [pis [_ [WF PROGRAM]]].
  inversion PROGRAM; subst pis.
  apply MemoryExtractor.check_extracted_wf_spec in WF as [_ ALL].
  apply Forall_forall; intros pi MEMBER.
  pose proof (@MemoryExtractor.Val.check_wf_polyinstr_affine_correct pi context vars
    (proj1 (forallb_forall _ _) ALL pi MEMBER)) as [WF [IDENTITY _]].
  unfold PL.wf_pinstr in WF; cbn zeta in WF.
  destruct WF as [_ [_ [_ [_ [DOMAIN [TRANSFORM [_ [SCHEDULE _]]]]]]]].
  unfold memory_identity_representation; split; [exact IDENTITY|].
  split; [apply memory_exact_columns_forall; exact DOMAIN|].
  split; [apply memory_exact_columns_forall; exact SCHEDULE|].
  apply memory_exact_columns_forall; rewrite IDENTITY in TRANSFORM; exact TRANSFORM.
Qed.
Fixpoint memory_reindexed_instructions dimension swaps instructions :=
  match swaps with
  | [] => instructions
  | position::rest => memory_reindexed_instructions dimension rest
      (memory_swap_instructions (dimension+position)%nat instructions)
  end.
Lemma memory_reindexed_identity_representation dimension swaps instructions :
  Forall (memory_identity_representation dimension) instructions ->
  Forall (memory_identity_representation dimension) (memory_reindexed_instructions dimension swaps instructions).
Proof.
  revert instructions; induction swaps; intros instructions REPRESENTATIONS; cbn; [exact REPRESENTATIONS|].
  apply IHswaps; unfold memory_swap_instructions; apply Forall_map; eapply Forall_impl; [|exact REPRESENTATIONS].
  intros pi REP; apply memory_swap_instruction_representation; exact REP.
Qed.
Theorem memory_reindexed_execution dimension swaps parameters instructions context vars initial final :
  length context = length parameters ->
  length parameters = dimension -> Forall (memory_identity_representation dimension) instructions ->
  (PL.poly_instance_list_semantics parameters (instructions,context,vars) initial final <->
   PL.poly_instance_list_semantics parameters (memory_reindexed_instructions dimension swaps instructions,context,vars) initial final).
Proof.
  revert instructions; induction swaps; intros instructions CONTEXT_LENGTH LENGTH REPRESENTATIONS; cbn; [reflexivity|].
  rewrite (@memory_coordinate_swap_execution (dimension+a)%nat parameters instructions context vars initial final
    CONTEXT_LENGTH ltac:(lia) ltac:(rewrite LENGTH; exact REPRESENTATIONS)).
  apply IHswaps; [exact CONTEXT_LENGTH|exact LENGTH|].
  unfold memory_swap_instructions; apply Forall_map; eapply Forall_impl; [|exact REPRESENTATIONS].
  intros pi REP; apply memory_swap_instruction_representation; exact REP.
Qed.
Definition memory_reindex_poly_program swaps (program : PL.t) :=
  let '(instructions,context,vars) := program in
  (memory_normalized_instructions (memory_reindexed_instructions (length context) swaps instructions),context,vars).

Definition representation_affine_term_eq_dec : forall first second : list Z * Z, {first = second} + {first <> second}.
Proof.
  intros [coefficients bias] [other_coefficients other_bias].
  destruct (@List.list_eq_dec Z Z.eq_dec coefficients other_coefficients) as [EQ|NE]; [subst|right; congruence].
  destruct (Z.eq_dec bias other_bias) as [EQ|NE]; [subst; left; reflexivity|right; congruence].
Defined.
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
  if @List.list_eq_dec (list Z * Z)%type representation_affine_term_eq_dec first second then pure true else
  BIND forward <- memory_check_domain_inclusion first second -;
  BIND backward <- memory_check_domain_inclusion second first -;
  pure (forward && backward).
Lemma memory_check_domain_equivalence_correct first second :
  mayReturn (memory_check_domain_equivalence first second) true ->
  forall index, in_poly index first = in_poly index second.
Proof.
  unfold memory_check_domain_equivalence; destruct (@List.list_eq_dec (list Z * Z)%type representation_affine_term_eq_dec first second) as [SAME|DIFFERENT].
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
  length context = length parameters ->
  mayReturn (memory_align_domains reference candidate) (Some aligned) ->
  (PL.poly_instance_list_semantics parameters (candidate,context,vars) initial final <->
   PL.poly_instance_list_semantics parameters (aligned,context,vars) initial final).
Proof.
  intros LENGTH CHECK; eapply memory_point_isomorphism_execution.
  - apply memory_domain_alignment_isomorphism; eapply memory_align_domains_correct; exact CHECK.
  - exact LENGTH.
Qed.
Print Assumptions memory_check_domain_equivalence_correct.
Print Assumptions memory_aligned_domains_execution.
Print Assumptions memory_extracted_identity_representation.
Print Assumptions memory_reindexed_execution.
End PolCertCandidateRepresentationFor.
