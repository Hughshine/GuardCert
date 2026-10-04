From Stdlib Require Import List.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values.
From compcert.cfrontend Require Import Clight.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestFirstLeaf AffineNestProbeRenaming.
Import ListNotations.
Set Implicit Arguments.

Definition affine_probe_needed nest prefix parameters := (prefix++parameters)++match nest with
  | AffineSourceLeaf _ => []
  | AffineSourceAxis iterator bound _ _ _ => [iterator;bound] end.
Definition affine_probe_stage_coverage registers nest prefix parameters :=
  forall identifier, In identifier((prefix++parameters)++affine_nest_controls nest) -> In identifier registers.

Lemma affine_probe_needed_covered registers nest prefix parameters :
  affine_probe_stage_coverage registers nest prefix parameters ->
  forall identifier, In identifier(affine_probe_needed nest prefix parameters) -> In identifier registers.
Proof.
  intros COVERAGE identifier MEMBER; apply COVERAGE.
  unfold affine_probe_needed in MEMBER; destruct nest; [exact MEMBER|].
  repeat rewrite in_app_iff in *; cbn [affine_nest_controls List.In] in *; tauto.
Qed.

Lemma affine_probe_stage_child_coverage registers prefix parameters iterator bound expression body child :
  affine_probe_stage_coverage registers(AffineSourceAxis iterator bound expression body child) prefix parameters ->
  affine_probe_stage_coverage registers child (prefix++[iterator]) parameters.
Proof.
  intros COVERAGE identifier MEMBER; apply COVERAGE.
  repeat rewrite in_app_iff in *; cbn [affine_nest_controls List.In] in *; tauto.
Qed.

Lemma affine_probe_stage_child_reads prefix parameters iterator bound expression body
  child_iterator child_bound child_expression child_body grandchild :
  affine_nest_bound_dependencies prefix parameters
    (AffineSourceAxis iterator bound expression body
      (AffineSourceAxis child_iterator child_bound child_expression child_body grandchild)) ->
  forall identifier, In identifier(memory_source_affine_reads child_expression) ->
    In identifier(affine_probe_needed (AffineSourceAxis iterator bound expression body
      (AffineSourceAxis child_iterator child_bound child_expression child_body grandchild)) prefix parameters).
Proof.
  intros [_ [READS _]] identifier MEMBER; specialize(READS identifier MEMBER).
  unfold affine_probe_needed; repeat rewrite in_app_iff in *; cbn [List.In] in *; tauto.
Qed.

(** Future public controls can be undefined. The input relation includes only
    earlier coordinates, stable parameters and the current header. The next
    header is added only after its two actual private assignments. *)
Lemma affine_probe_stage_child_view registers prefix parameters iterator bound expression body
  child_iterator child_bound child_expression child_body grandchild rename source target :
  affine_probe_stage_coverage registers (AffineSourceAxis iterator bound expression body
    (AffineSourceAxis child_iterator child_bound child_expression child_body grandchild)) prefix parameters ->
  affine_rename_injective registers rename ->
  affine_renamed_view (affine_probe_needed (AffineSourceAxis iterator bound expression body
    (AffineSourceAxis child_iterator child_bound child_expression child_body grandchild)) prefix parameters) rename source target ->
  affine_renamed_view (affine_probe_needed
    (AffineSourceAxis child_iterator child_bound child_expression child_body grandchild) (prefix++[iterator]) parameters)
    rename
    (affine_first_child_temps(AffineSourceAxis child_iterator child_bound child_expression child_body grandchild) source)
    (PTree.set (rename child_iterator)(Vint Int.zero)
      (PTree.set(rename child_bound)(Vint(Int.repr(memory_source_affine_math(affine_word_valuation source) child_expression))) target)).
Proof.
  intros COVERAGE UNIQUE VIEW.
  set (needed:=affine_probe_needed (AffineSourceAxis iterator bound expression body
    (AffineSourceAxis child_iterator child_bound child_expression child_body grandchild)) prefix parameters).
  assert (SUBSET:forall identifier, In identifier needed -> In identifier registers).
  { apply affine_probe_needed_covered; exact COVERAGE. }
  assert (CHILD_BOUND:In child_bound registers).
  { apply COVERAGE,in_or_app; right; cbn [affine_nest_controls List.In]; auto. }
  assert (CHILD_ITERATOR:In child_iterator registers).
  { apply COVERAGE,in_or_app; right; cbn [affine_nest_controls List.In]; auto. }
  pose proof(@affine_renamed_view_extend_set needed registers rename source target child_bound
    (Vint(Int.repr(memory_source_affine_math(affine_word_valuation source) child_expression)))
    UNIQUE SUBSET CHILD_BOUND VIEW) as FIRST.
  assert (SUBSET_NEXT:forall identifier, In identifier(needed++[child_bound]) -> In identifier registers).
  { intros identifier MEMBER; apply in_app_or in MEMBER; destruct MEMBER as [MEMBER|MEMBER]; [apply SUBSET; exact MEMBER|].
    cbn in MEMBER; destruct MEMBER as [SAME|BAD]; [subst; exact CHILD_BOUND|contradiction]. }
  pose proof(@affine_renamed_view_extend_set (needed++[child_bound]) registers rename _ _ child_iterator
    (Vint Int.zero) UNIQUE SUBSET_NEXT CHILD_ITERATOR FIRST) as SECOND.
  eapply affine_renamed_view_weaken; [|exact SECOND].
  intros identifier MEMBER; unfold needed,affine_probe_needed in *;
    repeat rewrite in_app_iff in *; cbn [List.In] in *; tauto.
Qed.
Print Assumptions affine_probe_stage_child_view.
