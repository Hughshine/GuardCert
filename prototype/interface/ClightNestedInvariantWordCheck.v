From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes Cop ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightNoWrap ClightRedundantSet.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation
  GuardMemoryAffineSourceReifier.
From GuardAffineNest Require Import AffineNestGuardPackage AffineNestStaticPackage.
From GuardInterface Require Import ClightNestedConstantSite ClightNestedConstantSiteFacts
  ClightNestedConstantSitePrepare ClightNestedConstantHeaders ClightNestedConstantStability
  ClightNestedInvariantWordModel CompCertInvariantWordObservation ClightInitializedBooleanAnd.
Import ListNotations.
Set Implicit Arguments.

(** This syntax walk proposes a value; the control and read-set checks below
    certify it. It does not infer assumptions for arbitrary program pairs. *)
Fixpoint first_store_value (body : statement) : option expr :=
  match body with
  | Sassign _ value => Some value
  | Ssequence first second | Sifthenelse _ first second =>
      match first_store_value first with Some value => Some value | None => first_store_value second end
  | _ => None end.

Definition ncs_invariant_expression parameters shape :=
  match ncs_stability_word shape with
  | Some _ => None (* Keep the established literal lowering. *)
  | None => match first_store_value (ncs_leaf shape) with
    | Some value => match propose_memory_source_affine value with
      | Some expression =>
        if check_invariant_word_control expression
          (ClightConstantBoundModel.constant_body_source (ncs_iterator shape)
            (Int.repr (ncs_upper shape)) (ncs_leaf shape)) &&
          affine_names_allocated_check (memory_source_affine_reads expression) parameters
        then Some expression else None
      | None => None end
    | None => None end
  end.

Theorem ncs_invariant_expression_sound parameters shape expression :
  ncs_invariant_expression parameters shape = Some expression ->
  check_invariant_word_control expression
    (ClightConstantBoundModel.constant_body_source (ncs_iterator shape)
      (Int.repr (ncs_upper shape)) (ncs_leaf shape)) = true /\
  incl (memory_source_affine_reads expression) parameters.
Proof.
  unfold ncs_invariant_expression; destruct (ncs_stability_word shape); [discriminate|].
  destruct (first_store_value (ncs_leaf shape)) as [value|]; [|discriminate].
  destruct (propose_memory_source_affine value) as [proposed|]; [|discriminate].
  destruct (check_invariant_word_control proposed _ && affine_names_allocated_check _ _) eqn:CHECK;
    [|discriminate].
  intro SAME; inversion SAME; subst proposed.
  apply andb_true_iff in CHECK as [BODY READS]; split; [exact BODY|].
  apply affine_names_allocated_check_sound; exact READS.
Qed.

Definition ncs_invariant_word expression temps :=
  Int.repr (memory_source_affine_math (memory_source_word_valuation temps) expression).

(** The old prepared receipt already obtains every parameter word from the
    reached original source. The new check adds no definedness callback. *)
Theorem ncs_prepared_invariant_value source parameters live proposal shape
  expression fe ge locals checked memory checked_source_after final
  (receipt : ncs_prepared_receipt source parameters live proposal shape
    fe ge locals checked memory checked_source_after final) :
  incl (memory_source_affine_reads expression) parameters ->
  eval_expr ge locals (ncs_prepared_temps shape checked) memory
    (memory_source_affine_code expression)
    (Vint (ncs_invariant_word expression (ncs_prepared_temps shape checked))).
Proof.
  intro READS; apply memory_source_affine_evaluation; intros identifier MEMBER.
  pose proof (ncs_prepare_domains receipt) as DOMAINS.
  apply Forall_forall with (x:=identifier) in DOMAINS; [|apply READS; exact MEMBER].
  destruct DOMAINS as [word WORD]; cbn [entry_temps] in WORD.
  unfold memory_source_word_valuation; rewrite WORD,Int.repr_signed; reflexivity.
Qed.

Definition ncs_invariant_equal_expression cache expression delta :=
  Ebinop Oeq (Etempvar cache type_int32s)
    (Ebinop Oadd (memory_source_affine_code expression) (Econst_int delta type_int32s) type_int32s)
    type_int32s.
Definition ncs_invariant_pair_expression shape expression :=
  initialized_boolean_and
    (ncs_invariant_equal_expression (ncs_root_cache shape) expression (ncs_delta shape))
    (ncs_invariant_equal_expression (ncs_child_cache shape) expression (ncs_child_delta shape)).

Lemma ncs_invariant_equal_evaluation ge locals temps memory cache expression delta word value :
  temps!cache = Some (Vint value) ->
  eval_expr ge locals temps memory (memory_source_affine_code expression) (Vint word) ->
  eval_expr ge locals temps memory (ncs_invariant_equal_expression cache expression delta)
    (Val.of_bool (Int.eq value (Int.add word delta))).
Proof.
  intros CACHE VALUE; unfold ncs_invariant_equal_expression.
  eapply eval_Ebinop with (v1:=Vint value) (v2:=Vint (Int.add word delta)).
  - constructor; exact CACHE.
  - eapply eval_Ebinop with (v1:=Vint word) (v2:=Vint delta).
    + exact VALUE.
    + constructor.
    + rewrite memory_source_affine_type; reflexivity.
  - reflexivity.
Qed.

Theorem ncs_invariant_pair_expression_test ge locals temps memory shape expression word root child :
  temps!(ncs_root_cache shape) = Some (Vint root) ->
  temps!(ncs_child_cache shape) = Some (Vint child) ->
  eval_expr ge locals temps memory (memory_source_affine_code expression) (Vint word) ->
  expression_test (ncs_invariant_pair_expression shape expression) (Entry ge locals temps memory)
    (ClightNestedConstantWordModel.ncs_same_word_flag shape word (Entry ge locals temps memory)).
Proof.
  intros ROOT CHILD VALUE; unfold ClightNestedConstantWordModel.ncs_same_word_flag;
    cbn [entry_temps]; unfold temp_word; rewrite ROOT,CHILD.
  eexists; split; [|apply bool_of_bool].
  unfold ncs_invariant_pair_expression.
  apply initialized_boolean_and_evaluation; [reflexivity|reflexivity| |].
  all: apply ncs_invariant_equal_evaluation; assumption.
Qed.

Print Assumptions ncs_invariant_expression_sound.
Print Assumptions ncs_prepared_invariant_value.
Print Assumptions ncs_invariant_equal_evaluation.
Print Assumptions ncs_invariant_pair_expression_test.
