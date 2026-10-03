From Stdlib Require Import List.
From Guard Require Import AbstractSchedule.
Import ListNotations.
Set Implicit Arguments.

Section INTERLEAVE.
Context {State Instruction : Type} (M : scheduling_model State Instruction).

Lemma certificate_suffix source target : schedule_certificate M source target ->
  forall suffix, schedule_certificate M (source ++ suffix) (target ++ suffix).
Proof.
  intro CERT; induction CERT; intro suffix; cbn.
  - constructor.
  - constructor; apply IHCERT.
  - apply certificate_swap; assumption.
  - eapply certificate_trans; eauto.
Qed.
Lemma certificate_prefix prefix source target : schedule_certificate M source target ->
  schedule_certificate M (prefix ++ source) (prefix ++ target).
Proof. intro CERT; induction prefix; cbn; [exact CERT|constructor; exact IHprefix]. Qed.
Lemma move_instruction_right instruction crossed suffix :
  (forall other, In other crossed -> independent M instruction other) ->
  schedule_certificate M (instruction :: crossed ++ suffix) (crossed ++ instruction :: suffix).
Proof.
  intro CROSS; induction crossed as [|other rest IH]; cbn; [constructor|].
  eapply certificate_trans.
  - apply certificate_swap, CROSS; cbn; auto.
  - constructor; apply IH; intros item MEMBER; apply CROSS; cbn; auto.
Qed.
Lemma swap_blocks first second suffix :
  (forall a b, In a first -> In b second -> independent M a b) ->
  schedule_certificate M (first ++ second ++ suffix) (second ++ first ++ suffix).
Proof.
  intro CROSS; induction first as [|a rest IH]; cbn; [constructor|].
  eapply certificate_trans with (middle := a :: second ++ rest ++ suffix).
  - apply certificate_head; apply IH; intros x y X Y; apply CROSS; cbn; auto.
  - apply move_instruction_right; intros b B; apply CROSS; cbn; auto.
Qed.
Lemma interleave_certificate {A} (first : A -> Instruction) (rest : A -> list Instruction) xs :
  (forall x y item, In x xs -> In y xs -> In item (rest y) -> independent M (first x) item) ->
  schedule_certificate M (map first xs ++ flat_map rest xs)
    (flat_map (fun x => first x :: rest x) xs).
Proof.
  intro CROSS; induction xs as [|x xs IH]; cbn; [constructor|].
  constructor; eapply certificate_trans with (middle := rest x ++ map first xs ++ flat_map rest xs).
  - apply swap_blocks; intros a b FIRST SECOND; apply in_map_iff in FIRST as [y [EQ Y]]; subst a.
    apply (CROSS y x b); cbn; auto.
  - apply certificate_prefix, IH; intros a b item FIRST SECOND ITEM.
    apply (CROSS a b item); cbn; auto.
Qed.

(** Dependence within each source row is preserved. Only operations from
    different rows have to commute. No trip counts are enumerated by this
    proof or by a compiler consuming its universally quantified premise. *)
Theorem rectangular_row_order_certificate {A B} (instruction : A -> B -> Instruction) rows columns :
  NoDup rows ->
  (forall row other column next,
    In row rows -> In other rows -> row <> other ->
    In column columns -> In next columns -> independent M (instruction row column) (instruction other next)) ->
  schedule_certificate M (flat_map (fun row => map (instruction row) columns) rows)
    (flat_map (fun column => map (fun row => instruction row column) rows) columns).
Proof.
  revert rows; intros rows UNIQUE CROSS; induction rows as [|row rows IH]; cbn.
  - clear CROSS; induction columns; cbn; [apply certificate_refl|exact IHcolumns].
  - inversion UNIQUE as [|? ? ABSENT TAIL]; subst.
    eapply certificate_trans with (middle := map (instruction row) columns ++
      flat_map (fun column => map (fun row => instruction row column) rows) columns).
    + apply certificate_prefix, IH; [exact TAIL|].
      intros a b x y FIRST SECOND NE X Y; apply CROSS; cbn; auto.
    + apply interleave_certificate; intros x y item X Y ITEM.
      apply in_map_iff in ITEM as [other [EQ OTHER]]; subst item.
      apply CROSS; cbn; auto; congruence.
Qed.
End INTERLEAVE.
Print Assumptions rectangular_row_order_certificate.
