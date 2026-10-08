(** Exact template deduplication above the semantic kernel.  Roots and complete
    affine maps must both agree; this does not infer semantic map equality. *)
From Stdlib Require Import List Bool ZArith Lia.
From polcert.src Require Import PolyBase.
From GuardMemory Require Import GuardMemoryBooleanScan GuardMemoryBooleanRectangle
  GuardMemoryMultiTensorAffineFootprint GuardMemoryCanonicalAlias.
Import ListNotations.
Set Implicit Arguments.

Definition access_template_eq_dec (first second : AccessFunction) :
    {first=second}+{first<>second}.
Proof.
  destruct (access_strict_eqb first second) eqn:CHECK.
  - left; apply access_strict_eqb_eq; exact CHECK.
  - right; intro SAME; pose proof (access_strict_eq_eqb first second SAME) as TRUE.
    rewrite CHECK in TRUE; discriminate.
Defined.

Definition deduplicate_access_templates := nodup access_template_eq_dec.
Definition access_templates_equivalent (first second : list AccessFunction) :=
  forall access, In access first <-> In access second.

Theorem deduplicate_access_templates_membership accesses :
  access_templates_equivalent (deduplicate_access_templates accesses) accesses.
Proof. intro access; apply nodup_In. Qed.

Theorem deduplicate_access_templates_unique accesses :
  NoDup (deduplicate_access_templates accesses).
Proof. apply NoDup_nodup. Qed.

Theorem deduplicate_access_templates_length accesses :
  length (deduplicate_access_templates accesses) <= length accesses.
Proof.
  eapply NoDup_incl_length; [apply deduplicate_access_templates_unique|].
  intros access MEMBER; apply deduplicate_access_templates_membership; exact MEMBER.
Qed.

Lemma access_template_map_membership {A} (f : AccessFunction -> A) first second :
  access_templates_equivalent first second ->
  forall value, In value (map f first) <-> In value (map f second).
Proof.
  intros SAME value; rewrite !in_map_iff; split; intros [access [VALUE MEMBER]].
  - exists access; split; [exact VALUE|apply SAME; exact MEMBER].
  - exists access; split; [exact VALUE|apply SAME; exact MEMBER].
Qed.

Lemma access_template_forallb_membership (test : AccessFunction -> bool) first second :
  access_templates_equivalent first second -> forallb test first = forallb test second.
Proof.
  intro SAME; apply Bool.eq_true_iff_eq; rewrite !forallb_forall.
  split; intros ALL access MEMBER; apply ALL; apply SAME; exact MEMBER.
Qed.

Lemma access_template_forallb_pointwise (first second : AccessFunction -> bool) accesses :
  (forall access, first access = second access) -> forallb first accesses = forallb second accesses.
Proof.
  intro SAME; induction accesses as [|access rest IH]; [reflexivity|].
  cbn; rewrite SAME,IH; reflexivity.
Qed.

Theorem access_template_point_check_exact locations first second values a b :
  access_templates_equivalent first second ->
  multi_tensor_affine_point_check locations first values a b =
  multi_tensor_affine_point_check locations second values a b.
Proof.
  intro SAME; unfold multi_tensor_affine_point_check.
  transitivity (forallb (fun left => forallb (fun right =>
    multi_tensor_affine_access_check locations left right (a++values) (b++values)) second) first).
  - apply access_template_forallb_pointwise; intro left; apply access_template_forallb_membership; exact SAME.
  - apply access_template_forallb_membership; exact SAME.
Qed.

Lemma access_template_rectangle_ext (first second : list Z -> bool) counts :
  (forall point, first point = second point) -> forall prefix,
  memory_boolean_rectangle_result first counts prefix =
  memory_boolean_rectangle_result second counts prefix.
Proof.
  intro SAME; induction counts as [|count rest IH]; intro prefix; [apply SAME|].
  cbn [memory_boolean_rectangle_result]; apply memory_boolean_scan_ext; intro coordinate; apply IH.
Qed.

Theorem access_template_canonical_check_exact locations first second values counts :
  access_templates_equivalent first second ->
  canonical_alias_check locations first values counts = canonical_alias_check locations second values counts.
Proof.
  intro SAME; unfold canonical_alias_check; apply access_template_rectangle_ext; intro point.
  apply access_template_point_check_exact; exact SAME.
Qed.

Example repeated_two_root_templates :
  let accesses : list AccessFunction := [(1%positive,[([16%Z;1%Z],0%Z)]); (2%positive,[([16%Z;1%Z],0%Z)]);
    (2%positive,[([16%Z;1%Z],0%Z)]); (1%positive,[([16%Z;1%Z],0%Z)])] in
  length accesses = 4 /\ length (deduplicate_access_templates accesses) = 2.
Proof. vm_compute; auto. Qed.

Print Assumptions deduplicate_access_templates_membership.
Print Assumptions deduplicate_access_templates_unique.
Print Assumptions deduplicate_access_templates_length.
Print Assumptions access_template_map_membership.
Print Assumptions access_template_point_check_exact.
Print Assumptions access_template_canonical_check_exact.
Print Assumptions repeated_two_root_templates.
