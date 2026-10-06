From Stdlib Require Import List Bool.
From compcert.lib Require Import Coqlib Maps.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightTempFootprint.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions GuardMemoryAffineInnerPointerSyntax
  GuardMemoryNaryCompute GuardMemoryNaryAffineAccess GuardMemoryAffineCursorProbes GuardMemoryAffineNestedCursorProbes.
From GuardInterface Require Import ClightAffineDependentCursorScan ClightCheckPlan.
Import ListNotations.
Set Implicit Arguments.

Definition cursor_names_disjoint names protected :=
  forallb (fun id => if in_dec peq id protected then false else true) names.
Lemma cursor_names_disjoint_sound names protected : cursor_names_disjoint names protected=true ->
  forall id, In id names -> ~ In id protected.
Proof.
  intros CHECK id MEMBER; unfold cursor_names_disjoint in CHECK.
  apply forallb_forall with (x:=id) in CHECK; [|exact MEMBER].
  destruct (in_dec peq id protected); [discriminate|assumption].
Qed.
Definition cursor_read_scope_check cursor public reads :=
  forallb (fun id => if peq id cursor then true else if in_dec peq id public then true else false) reads.
Lemma cursor_read_scope_check_sound cursor public reads : cursor_read_scope_check cursor public reads=true ->
  forall id, In id reads -> id <> cursor -> In id public.
Proof.
  intros CHECK id MEMBER OTHER; unfold cursor_read_scope_check in CHECK.
  apply forallb_forall with (x:=id) in CHECK; [|exact MEMBER].
  destruct (peq id cursor); [contradiction|destruct (in_dec peq id public); [assumption|discriminate]].
Qed.

Definition affine_cursor_external_reads row column reads :=
  filter (fun id => if peq id row then false else if peq id column then false else true) reads.
Lemma affine_cursor_external_reads_member row column reads id :
  In id (affine_cursor_external_reads row column reads) <-> In id reads /\ id <> row /\ id <> column.
Proof.
  unfold affine_cursor_external_reads; rewrite filter_In; destruct (peq id row); destruct (peq id column); cbn; intuition congruence.
Qed.
Definition affine_cursor_operations_check row column outer inner operations :=
  forallb (fun operation => cursor_names_disjoint [outer;inner]
    (memory_nary_access_array (memory_nary_compute_write operation)::affine_cursor_external_reads row column
      (memory_source_affine_reads (memory_nary_access_expression (memory_nary_compute_write operation))))) operations.

Lemma affine_cursor_operations_check_sound row column outer inner operations :
  affine_cursor_operations_check row column outer inner operations=true ->
  Forall (memory_affine_nested_cursor_operation_fresh row column outer inner) operations.
Proof.
  intro CHECK; apply Forall_forall; intros operation MEMBER.
  unfold affine_cursor_operations_check in CHECK; apply forallb_forall with (x:=operation) in CHECK; [|exact MEMBER].
  pose proof (@cursor_names_disjoint_sound _ _ CHECK) as FRESH.
  assert (ONE : forall cursor, In cursor [outer;inner] -> memory_affine_cursor_operation_fresh row column cursor operation).
  { intros cursor USED; split.
    - intro SAME; apply (@FRESH cursor USED); left; exact SAME.
    - intros id READ ROW COLUMN SAME; subst id; apply (@FRESH cursor USED); right.
      apply affine_cursor_external_reads_member; auto. }
  split; apply ONE; cbn; auto.
Qed.

Record affine_dependent_cursor_resources source (package : memory_affine_inner_pointer_package source)
  root pointer_cache outer inner result live : Prop := {
  cursor_resources_distinct : outer <> inner /\ outer <> result /\ inner <> result;
  cursor_resources_private : ~ In outer live /\ ~ In inner live /\ ~ In result live;
  cursor_resources_inputs : affine_inner_pointer_bound (affine_inner_pointer_shape package) <> outer /\
    (root <> outer /\ root <> inner) /\ (pointer_cache <> outer /\ pointer_cache <> inner);
  cursor_resources_bound : forall id, In id (memory_source_affine_reads (affine_inner_pointer_expression package)) ->
    id <> affine_inner_pointer_row (affine_inner_pointer_shape package) ->
    id <> affine_inner_pointer_column (affine_inner_pointer_shape package) -> id <> outer /\ id <> inner;
  cursor_resources_operations : Forall (memory_affine_nested_cursor_operation_fresh
    (affine_inner_pointer_row (affine_inner_pointer_shape package))
    (affine_inner_pointer_column (affine_inner_pointer_shape package)) outer inner) (affine_inner_pointer_operations package);
  cursor_resources_result : ~ In result (check_plan_reads (tree_check_plan (affine_dependent_cursor_probe package root pointer_cache outer inner)));
  cursor_resources_outer_reads : forall id, In id (expression_temps (affine_dependent_cursor_outer package outer)) -> id <> outer -> In id live;
  cursor_resources_inner_reads : forall id, In id (expression_temps (affine_dependent_cursor_inner package outer inner)) -> id <> inner -> In id (outer::live);
  cursor_resources_point_reads : forall id, In id (check_plan_reads (tree_check_plan (affine_dependent_cursor_probe package root pointer_cache outer inner))) ->
    id <> inner -> In id (outer::live)
}.

(** These are finite syntax/resource checks. They do not build the unfolded
    stability tree or depend on the row and column caps. *)
Definition affine_dependent_cursor_resources_check source (package : memory_affine_inner_pointer_package source)
  root pointer_cache outer inner result live :=
  (if peq outer inner then false else if peq outer result then false else if peq inner result then false else true) &&
  (cursor_names_disjoint [outer;inner;result] live &&
  (cursor_names_disjoint [outer;inner] [affine_inner_pointer_bound (affine_inner_pointer_shape package);root;pointer_cache] &&
  (cursor_names_disjoint [outer;inner] (affine_cursor_external_reads
    (affine_inner_pointer_row (affine_inner_pointer_shape package)) (affine_inner_pointer_column (affine_inner_pointer_shape package))
    (memory_source_affine_reads (affine_inner_pointer_expression package))) &&
  (affine_cursor_operations_check (affine_inner_pointer_row (affine_inner_pointer_shape package))
    (affine_inner_pointer_column (affine_inner_pointer_shape package)) outer inner (affine_inner_pointer_operations package) &&
  (cursor_names_disjoint [result] (check_plan_reads (tree_check_plan (affine_dependent_cursor_probe package root pointer_cache outer inner))) &&
  (cursor_read_scope_check outer live (expression_temps (affine_dependent_cursor_outer package outer)) &&
  (cursor_read_scope_check inner (outer::live) (expression_temps (affine_dependent_cursor_inner package outer inner)) &&
   cursor_read_scope_check inner (outer::live) (check_plan_reads (tree_check_plan (affine_dependent_cursor_probe package root pointer_cache outer inner)))))))))).

Theorem affine_dependent_cursor_resources_sound source (package : memory_affine_inner_pointer_package source)
  root pointer_cache outer inner result live :
  affine_dependent_cursor_resources_check package root pointer_cache outer inner result live=true ->
  affine_dependent_cursor_resources package root pointer_cache outer inner result live.
Proof.
  unfold affine_dependent_cursor_resources_check; rewrite !andb_true_iff.
  intros [DISTINCT [PRIVATE [INPUTS [BOUND [OPERATIONS [RESULT [OUTER [INNER POINT]]]]]]]].
  pose proof (@cursor_names_disjoint_sound _ _ PRIVATE) as PRIVATE_NAMES.
  pose proof (@cursor_names_disjoint_sound _ _ INPUTS) as INPUT_NAMES.
  pose proof (@cursor_names_disjoint_sound _ _ BOUND) as BOUND_NAMES.
  constructor.
  - destruct (peq outer inner); [discriminate|destruct (peq outer result); [discriminate|destruct (peq inner result); [discriminate|auto]]].
  - repeat split; eapply PRIVATE_NAMES; cbn; auto.
  - assert (FIRST : ~ In outer [affine_inner_pointer_bound (affine_inner_pointer_shape package);root;pointer_cache]) by
      (apply INPUT_NAMES; cbn; auto).
    assert (SECOND : ~ In inner [affine_inner_pointer_bound (affine_inner_pointer_shape package);root;pointer_cache]) by
      (apply INPUT_NAMES; cbn; auto).
    cbn in FIRST,SECOND; intuition congruence.
  - intros id READ ROW COLUMN; assert (MEMBER : In id (affine_cursor_external_reads
      (affine_inner_pointer_row (affine_inner_pointer_shape package)) (affine_inner_pointer_column (affine_inner_pointer_shape package))
      (memory_source_affine_reads (affine_inner_pointer_expression package)))) by (apply affine_cursor_external_reads_member; auto).
    split; intro SAME; subst id; [apply (@BOUND_NAMES outer)|apply (@BOUND_NAMES inner)]; cbn; auto.
  - apply affine_cursor_operations_check_sound; exact OPERATIONS.
  - apply (@cursor_names_disjoint_sound [result] _ RESULT result); cbn; auto.
  - apply cursor_read_scope_check_sound; exact OUTER.
  - apply cursor_read_scope_check_sound; exact INNER.
  - apply cursor_read_scope_check_sound; exact POINT.
Qed.

Print Assumptions cursor_names_disjoint_sound.
Print Assumptions cursor_read_scope_check_sound.
Print Assumptions affine_cursor_external_reads_member.
Print Assumptions affine_cursor_operations_check_sound.
Print Assumptions affine_dependent_cursor_resources_sound.
