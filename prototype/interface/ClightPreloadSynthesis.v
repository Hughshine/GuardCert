From Stdlib Require Import Bool.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From Guard Require Import AbstractGuard SemanticFacts ClightCondition.
From GuardInterface Require Import GuardInterface GuardedRewrite ClightReadonlyRewrite ClightPreloadExample.
Set Implicit Arguments.

(** This is a specification of the atom's checked result. The runtime code
    does not query Mem.loadv or permission metadata: it tests the count, then
    uses an ordinary Clight load on the source-active path. *)
Definition preload_decide count pointer entry : option bool :=
  match (entry_temps entry) ! count with
  | Some (Vint x) =>
      if word_truth x then
        match (entry_temps entry) ! pointer with
        | Some (Vptr b offset) =>
            match Mem.loadv Mint32 (entry_memory entry) (Vptr b offset) with
            | Some (Vint value) => Some (word_truth value)
            | _ => None
            end
        | _ => None
        end
      else None
  | _ => None
  end.

Definition preload_dimension count pointer :
  property_dimension clight_entry unit (preload_domain count pointer).
Proof.
  refine {| atom_property := fun _ => preload_premise count pointer;
    decide_atom := fun _ => preload_decide count pointer |}.
  intros atom entry accepted [x [LOOKUP LOAD_IF_ACTIVE]] DECIDE.
  unfold preload_decide in DECIDE; rewrite LOOKUP in DECIDE.
  destruct (word_truth x) eqn:ACTIVE; [|discriminate].
  destruct (LOAD_IF_ACTIVE eq_refl) as [b [offset [value [POINTER LOAD]]]].
  rewrite POINTER, LOAD in DECIDE; injection DECIDE as RESULT; subst accepted.
  destruct (word_truth value) eqn:POSITIVE; cbn [decision_evidence].
  - split.
    + apply (proj2 (count_test_exact count entry LOOKUP true)); symmetry; exact ACTIVE.
    + apply (proj2 (bound_load_test_exact pointer entry POINTER LOAD true)); symmetry; exact POSITIVE.
  - intros [_ BOUND]; apply (proj1 (bound_load_test_exact pointer entry POINTER LOAD true)) in BOUND.
    rewrite POSITIVE in BOUND; discriminate.
Defined.

Definition preload_primitives count pointer :
  check_primitives decision_language (preload_domain count pointer)
    (decide_atom (preload_dimension count pointer)).
Proof.
  refine (@CheckPrimitives clight_entry unit decision_language (preload_domain count pointer)
    (decide_atom (preload_dimension count pointer))
    (fun _ => count_test count) (fun _ => bound_load pointer) _ _).
  - intros atom entry accepted [x [LOOKUP LOAD_IF_ACTIVE]].
    cbn [preload_dimension decide_atom]; unfold preload_decide; rewrite LOOKUP.
    rewrite (count_test_exact count entry LOOKUP accepted).
    destruct (word_truth x) eqn:ACTIVE; [|reflexivity].
    destruct (LOAD_IF_ACTIVE eq_refl) as [b [offset [value [POINTER LOAD]]]].
    rewrite POINTER, LOAD; reflexivity.
  - intros atom entry accepted expected [x [LOOKUP LOAD_IF_ACTIVE]] DECIDE.
    cbn [preload_dimension decide_atom] in DECIDE; unfold preload_decide in DECIDE; rewrite LOOKUP in DECIDE.
    destruct (word_truth x) eqn:ACTIVE; [|discriminate].
    destruct (LOAD_IF_ACTIVE eq_refl) as [b [offset [value [POINTER LOAD]]]].
    rewrite POINTER, LOAD in DECIDE; injection DECIDE as SAME; subst expected.
    exact (bound_load_test_exact pointer entry POINTER LOAD accepted).
Defined.

Theorem synthesized_preload_is_lazy count pointer :
  synthesize_tree (preload_primitives count pointer) (Fact tt) = lazy_preload_tree count pointer.
Proof. reflexivity. Qed.

Definition synthesized_preload_condition fe O (observe : fragment_observation -> O -> Prop)
  count pointer (premise : formula unit) :
  readonly_condition (readonly_clight_host fe observe) (preload_domain count pointer)
    (fun entry => formula_property (fun _ => preload_premise count pointer) premise entry)
    (synthesize_tree (preload_primitives count pointer) premise) :=
  synthesized_readonly_condition fe observe (preload_dimension count pointer)
    (preload_primitives count pointer) premise.

Example empty_path_negation_still_refuses count pointer entry :
  (entry_temps entry) ! count = Some (Vint Int.zero) ->
  formula_accepts (decide_atom (preload_dimension count pointer)) (Complement (Fact tt)) entry = false.
Proof.
  intro LOOKUP.
  assert (UNKNOWN : decide_atom (preload_dimension count pointer) tt entry = None).
  { change (preload_decide count pointer entry = None).
    unfold preload_decide; rewrite LOOKUP; reflexivity. }
  unfold formula_accepts; cbn [formula_execute]; rewrite UNKNOWN; reflexivity.
Qed.

Print Assumptions preload_dimension.
Print Assumptions preload_primitives.
Print Assumptions synthesized_preload_is_lazy.
Print Assumptions synthesized_preload_condition.
Print Assumptions empty_path_negation_still_refuses.
