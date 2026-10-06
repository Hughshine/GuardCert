From Stdlib Require Import Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import SemanticFacts ClightNoWrap ClightCondition ClightPureExpr ClightCountedProtocol ClightRegionProgress.
From GuardInterface Require Import ClightCounterProgress ClightCircularCounter ClightCircularMachine.
Set Implicit Arguments.

(** The cached candidate has a finite modular-distance protocol. This progress
    certificate is deliberately not a certificate for the uncached source. *)
Definition circular_candidate_counter iterator cache (DISTINCT : iterator <> cache) :
  counter_progress_facts iterator (circular_increment_expression iterator).
Proof.
  pose (OLD := circular_counter_facts DISTINCT).
  refine (@CounterProgressFacts iterator (circular_increment_expression iterator)
    (circular_active iterator cache) (circular_remaining iterator cache) (increment_temps iterator) _ _ _ _).
  - exact (counter_model_positive OLD).
  - exact (counter_model_distance OLD).
  - intros ge locals le m [word [upper [ITER [CACHE APART]]]].
    exists (Vint (Int.add word Int.one)); split.
    + eapply eval_Ebinop with (v1 := Vint word) (v2 := Vint Int.one);
        [apply eval_Etempvar; exact ITER | constructor | reflexivity].
    + unfold increment_temps; rewrite ITER; reflexivity.
  - repeat constructor.
Defined.

Lemma circular_cached_test_active ge locals le m iterator cache :
  expression_test (circular_cached_test iterator cache) (Entry ge locals le m) true ->
  circular_active iterator cache le.
Proof.
  intros [value [EVAL BOOL]]; apply scalar_binary_inv in EVAL.
  destruct EVAL as [word [upper [ITER [CACHE OP]]]].
  apply scalar_temp_inv in ITER, CACHE; destruct word, upper; try discriminate OP.
  change (Some (Val.of_bool (negb (Int.eq i i0))) = Some value) in OP.
  injection OP as SAME; subst value; rewrite bool_of_bool in BOOL.
  injection BOOL as BOOL; apply negb_true_iff in BOOL; exists i, i0; split; [exact ITER | split; [exact CACHE |]].
  pose proof (Int.eq_spec i i0); rewrite BOOL in H; exact H.
Qed.
Definition circular_cached_progress iterator out cache (DISTINCT : iterator <> cache) :
  region_progress (circular_memory_loop iterator out (circular_cached_test iterator cache)).
Proof.
  apply generic_frontend_progress with (FACTS := circular_candidate_counter DISTINCT); [reflexivity |].
  intros ge locals le m TEST; eapply circular_cached_test_active; exact TEST.
Defined.

Print Assumptions circular_candidate_counter.
Print Assumptions circular_cached_test_active.
Print Assumptions circular_cached_progress.
