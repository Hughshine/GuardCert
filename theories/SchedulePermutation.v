From Stdlib Require Import List Sorting.Permutation.
From Guard Require Import AbstractSchedule.
Import ListNotations.
Set Implicit Arguments.

Section PERMUTATIONS.
Context {S Instruction : Type} (M : scheduling_model S Instruction).
Variable eq_instruction : forall a b : Instruction, {a = b} + {a <> b}.

Theorem independent_permutation_certificate source target :
  Permutation source target ->
  (forall a b, In a source -> In b source -> a <> b -> independent M a b) ->
  schedule_certificate M source target.
Proof.
  intro ORDER; induction ORDER; intro INDEPENDENT.
  - constructor.
  - apply certificate_head, IHORDER. intros a b A B NE.
    apply INDEPENDENT; cbn; auto.
  - destruct (eq_instruction y x) as [EQ|NE].
    + subst y; constructor.
    + apply certificate_swap, INDEPENDENT; cbn; auto.
  - eapply certificate_trans; [apply IHORDER1; exact INDEPENDENT|].
    apply IHORDER2; intros a b A B NE; apply INDEPENDENT; auto.
    + eapply Permutation_in; [apply Permutation_sym; exact ORDER1|exact A].
    + eapply Permutation_in; [apply Permutation_sym; exact ORDER1|exact B].
Qed.
End PERMUTATIONS.

Lemma interleave_flat_map_permutation {A B} (f : A -> B) (g : A -> list B) xs :
  Permutation (map f xs ++ flat_map g xs)
    (flat_map (fun x => f x :: g x) xs).
Proof.
  induction xs as [|x xs IH]; cbn; [constructor|].
  apply perm_skip.
  eapply Permutation_trans with (l' := g x ++ map f xs ++ flat_map g xs).
  - apply Permutation_app_swap_app.
  - apply Permutation_app_head; exact IH.
Qed.

Theorem rectangular_order_permutation {A B C} (f : A -> B -> C) xs ys :
  Permutation (flat_map (fun x => map (f x) ys) xs)
    (flat_map (fun y => map (fun x => f x y) xs) ys).
Proof.
  induction xs as [|x xs IH].
  - cbn. induction ys; cbn; auto.
  - cbn [flat_map].
    eapply Permutation_trans.
    + apply Permutation_app_head; exact IH.
    + apply interleave_flat_map_permutation.
Qed.

Print Assumptions independent_permutation_certificate.
Print Assumptions rectangular_order_permutation.
