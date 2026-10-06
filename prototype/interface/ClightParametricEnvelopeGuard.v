From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Integers.
From Guard Require Import ClightCondition ClightPureExpr ClightGuard ClightNoWrap ClightRectangularGuard ClightRectangularStore.
From GuardMemory Require Import GuardMemoryArrayBackend GuardMemoryRegistryGuard GuardMemoryParametricGuard GuardMemoryParametricWidth.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ClightReadonlyCheckReplacement ClightParametricEnvelope.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition choose_parametric_envelope_width stride row context bounds expression original :=
  if Nat.eqb (length bounds) (length context) then
    match compile_parametric_envelope_width stride row context bounds expression with
    | Some replacement => replacement | None => original end
  else original.

Lemma parametric_envelope_prefix base descriptors row bound parameters bounds expression entry :
  rectangle_layout_valid base ->
  memory_source_guard_domain base descriptors row bound (bound::parameters) bounds expression entry ->
  decision_run entry (memory_source_header_tree base row bound) true ->
  decision_run entry (MemorySourceRanges.range_guard (bound::parameters) bounds) true ->
  MemoryNested.A.typed_view (bound::parameters) (memory_source_parameter_values (bound::parameters) entry) (entry_temps entry) /\
  MemoryNested.A.env_within bounds (memory_source_parameter_values (bound::parameters) entry) /\
  0 < Int.signed (temp_word bound (entry_temps entry)).
Proof.
  intros VALID [ROW [BOUND [PARAMETERS ARRAYS]]] HEADER RANGE.
  apply (proj1 (@memory_source_header_exact base row bound entry ROW BOUND true)) in HEADER.
  pose proof (PARAMETERS (eq_sym HEADER)) as VIEW.
  split; [exact VIEW|split].
  - eapply MemorySourceRanges.range_guard_sound; [exact VIEW|exact RANGE].
  - destruct (@memory_source_header_sound base row bound entry VALID ROW BOUND (eq_sym HEADER))
      as [_ [_ [COUNT _]]]; exact COUNT.
Qed.

(** Refusal by the static encoder keeps the old width check. Runtime refusal
    selects the original source. Neither path changes the entry domain. *)
Definition parametric_envelope_guard_condition fe O (observe : fragment_observation -> O -> Prop)
  base (VALID : rectangle_layout_valid base) descriptors row bound parameters bounds expression original premise
  (LOWER : compile_memory_source_width (rectangle_stride base) row (bound::parameters) bounds expression = Some original)
  (OLD : readonly_condition (readonly_clight_host fe observe)
    (memory_source_guard_domain base descriptors row bound (bound::parameters) bounds expression) premise
    (memory_source_guard_tree base descriptors row bound (bound::parameters) bounds original)) :
  readonly_condition (readonly_clight_host fe observe)
    (memory_source_guard_domain base descriptors row bound (bound::parameters) bounds expression) premise
    (memory_source_guard_tree base descriptors row bound (bound::parameters) bounds
      (choose_parametric_envelope_width (rectangle_stride base) row (bound::parameters) bounds expression original)).
Proof.
  unfold choose_parametric_envelope_width.
  destruct (Nat.eqb (length bounds) (length (bound::parameters))) eqn:ARITY; [|exact OLD].
  apply Nat.eqb_eq in ARITY.
  destruct (compile_parametric_envelope_width (rectangle_stride base) row (bound::parameters) bounds expression)
    as [replacement|] eqn:COMPILE; [|exact OLD].
  eapply replace_readonly_stage; [exact OLD| |].
  - intros [ge locals temps memory] DOMAIN HEADER RANGE.
    destruct (@parametric_envelope_prefix base descriptors row bound parameters bounds expression _ VALID DOMAIN HEADER RANGE)
      as [VIEW [WITHIN COUNT]].
    exact (proj1 (@compile_parametric_envelope_width_correct (rectangle_stride base) row bound parameters bounds expression
      replacement (fun id => Int.signed (temp_word id temps)) ge locals temps memory COMPILE ARITY VIEW WITHIN COUNT)).
  - intros [ge locals temps memory] DOMAIN HEADER RANGE ACCEPT.
    destruct (@parametric_envelope_prefix base descriptors row bound parameters bounds expression _ VALID DOMAIN HEADER RANGE)
      as [VIEW [WITHIN COUNT]].
    exact (@parametric_envelope_refines_width (rectangle_stride base) row bound parameters bounds expression replacement original
      (fun id => Int.signed (temp_word id temps)) ge locals temps memory COMPILE LOWER ARITY VIEW WITHIN COUNT ACCEPT).
Defined.
Print Assumptions parametric_envelope_prefix.
Print Assumptions parametric_envelope_guard_condition.
