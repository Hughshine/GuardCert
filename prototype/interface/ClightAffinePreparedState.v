From Stdlib Require Import List ZArith Lia Bool.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightGuard ClightNoWrap ClightCountedLoop
  ClightTempFrame ClightPureExpr ClightLoopSyntax ClightRegionProgress ClightStraightLine
  ClightRedundantSet ClightRectangularGuard ClightFrontendLoopProtocol ClightRectangularLoops.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryNaryCompute GuardMemoryNaryRanges
  GuardMemoryRecursiveSource GuardMemoryScalarPointerBody GuardMemorySourceParameters
  GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation GuardMemoryAffineSourceContext
  GuardMemoryAffineSourceLoop GuardMemoryParametricGuard GuardMemoryParametricSourceDomain
  GuardMemoryParametricSourceClight GuardMemoryParametricFirstBody GuardMemoryAffinePointerBody
  GuardMemoryAffineInnerPointerSyntax GuardMemoryAffineInnerPointerSourceDomain
  GuardMemoryAffineInnerPointerRegionSource GuardMemoryMultiPointerSequence
  GuardMemoryPointerSequence GuardMemoryLoadedExternalTransport GuardMemoryAffineAddressSpecialization.
From GuardInterface Require Import ClightAffineInnerPointerSourceGuard.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition affine_prepared_valuation entry identifier := Int.signed (temp_word identifier (entry_temps entry)).
Definition affine_prepared_count source (package : memory_affine_inner_pointer_package source) entry :=
  affine_prepared_valuation entry (affine_inner_pointer_bound (affine_inner_pointer_shape package)).
Definition affine_prepared_upper source (package : memory_affine_inner_pointer_package source) entry i :=
  L.eval_expr (i::memory_source_parameter_values (memory_affine_inner_pointer_region_context package) entry)
    (affine_inner_pointer_encoded package).
Definition affine_prepared_point_values source (package : memory_affine_inner_pointer_package source) entry i j :=
  ([i;j]++memory_source_parameter_values (affine_inner_pointer_geometry package) entry)++
    memory_source_parameter_values (affine_inner_pointer_scalars package) entry.
Definition affine_prepared_point source (package : memory_affine_inner_pointer_package source) entry i j :=
  memory_multi_pointer_sequence_physical (entry_temps entry) (affine_prepared_point_values package entry i j)
    (affine_inner_pointer_operations package).
Definition affine_prepared_body_stable source (package : memory_affine_inner_pointer_package source) :=
  affine_inner_pointer_pointers package++memory_affine_inner_pointer_region_context package.
Definition affine_prepared_stable source (package : memory_affine_inner_pointer_package source) pointer :=
  pointer::affine_prepared_body_stable package.

Section STATE.
Variable source : statement.
Variable package : memory_affine_inner_pointer_package source.
Let shape := affine_inner_pointer_shape package.
Let row := affine_inner_pointer_row shape.
Let cache := affine_inner_pointer_bound shape.
Let column := affine_inner_pointer_column shape.
Let inner_bound := affine_inner_pointer_inner_bound shape.
Let expression := affine_inner_pointer_expression package.
Let parameters := affine_inner_pointer_geometry package.
Let context := memory_affine_inner_pointer_region_context package.
Let CERT := affine_inner_pointer_syntax package.

Lemma affine_prepared_protected identifier : In identifier (affine_prepared_body_stable package) ->
  identifier <> row /\ identifier <> column /\ identifier <> inner_bound.
Proof.
  intro MEMBER; pose proof (affine_inner_pointer_protected CERT MEMBER) as FRESH.
  repeat split; intro SAME; apply FRESH; subst identifier; cbn; auto.
Qed.

Lemma affine_prepared_context_protected identifier : In identifier context ->
  identifier <> row /\ identifier <> column /\ identifier <> inner_bound.
Proof. intro MEMBER; apply affine_prepared_protected; apply in_or_app; right; exact MEMBER. Qed.

Lemma affine_prepared_words entry : affine_inner_pointer_ready package entry ->
  forall identifier, In identifier context ->
    (entry_temps entry) ! identifier = Some (Vint (Int.repr (affine_prepared_valuation entry identifier))).
Proof.
  intros READY identifier MEMBER.
  destruct (@memory_source_typed_word _ _ _ identifier (affine_inner_pointer_ready_view READY) MEMBER) as [word LOOK].
  unfold affine_prepared_valuation,temp_word; rewrite LOOK,Int.repr_signed; reflexivity.
Qed.

Lemma affine_prepared_cache_domain entry : affine_inner_pointer_ready package entry -> register_domain cache entry.
Proof.
  intro READY; eexists; apply affine_prepared_words; [exact READY|].
  unfold context,memory_affine_inner_pointer_region_context,memory_affine_inner_pointer_parameters,
    memory_affine_inner_pointer_header,memory_source_context; apply in_or_app; left; cbn; auto.
Qed.

Lemma affine_prepared_count_range entry : affine_inner_pointer_ready package entry ->
  0 < affine_prepared_count package entry <= affine_inner_pointer_row_limit package.
Proof.
  intro READY; pose proof (affine_inner_pointer_ready_header READY) as HEADER.
  unfold memory_affine_inner_pointer_header_accept in HEADER; apply andb_true_iff in HEADER as [_ RANGE].
  assert (CAP : signed_range (affine_inner_pointer_row_limit package)).
  { pose proof (affine_inner_pointer_control_limits CERT) as CAPS; inversion CAPS; subst; tauto. }
  exact (proj2 (@register_range_sound cache (affine_inner_pointer_row_limit package) entry CAP
    (affine_prepared_cache_domain READY) RANGE)).
Qed.

Lemma affine_prepared_upper_math entry i : affine_prepared_upper package entry i =
  memory_source_affine_math (memory_source_set_valuation (affine_prepared_valuation entry) row i) expression.
Proof.
  unfold affine_prepared_upper,affine_prepared_valuation,memory_affine_inner_pointer_region_context,
    memory_source_parameter_values.
  apply memory_source_loop_expression_value; exact (affine_inner_pointer_full_encoding CERT).
Qed.

Lemma affine_prepared_upper_range entry i : affine_inner_pointer_ready package entry ->
  0 <= i < affine_prepared_count package entry ->
  (0 <= affine_prepared_upper package entry i <= affine_inner_pointer_column_limit package) /\
    signed_range (affine_prepared_upper package entry i).
Proof.
  intros READY I; rewrite affine_prepared_upper_math.
  pose proof (affine_inner_pointer_ready_width READY) as WIDTH.
  unfold memory_affine_inner_pointer_width_property in WIDTH.
  assert (RANGE : 0 <= memory_source_affine_math
    (memory_source_set_valuation (affine_prepared_valuation entry) row i) expression <= affine_inner_pointer_column_limit package).
  { unfold affine_prepared_valuation; rewrite <- memory_affine_inner_pointer_word_math.
    apply (proj2 WIDTH); rewrite memory_source_word_temp; exact I. }
  assert (CAP : signed_range (affine_inner_pointer_column_limit package)).
  { pose proof (affine_inner_pointer_control_limits CERT) as CAPS; inversion CAPS; subst;
    match goal with REST : Forall _ [_] |- _ => inversion REST; subst; tauto end. }
  split; [exact RANGE|unfold signed_range in *; change Int.min_signed with (-2147483648) in *; lia].
Qed.

Lemma affine_prepared_header_read identifier : In identifier (memory_source_affine_reads expression) -> identifier <> row ->
  In identifier context.
Proof.
  intros READ OTHER; unfold context,memory_affine_inner_pointer_region_context;
    apply in_or_app; left; unfold memory_affine_inner_pointer_parameters;
    apply in_or_app; left; apply memory_source_context_read; assumption.
Qed.

Lemma affine_prepared_upper_value entry i current memory : affine_inner_pointer_ready package entry ->
  current ! row = Some (Vint (Int.repr i)) ->
  temp_agree (affine_prepared_body_stable package) (entry_temps entry) current ->
  eval_expr (entry_ge entry) (entry_env entry) current memory (memory_source_affine_code expression)
    (Vint (Int.repr (affine_prepared_upper package entry i))).
Proof.
  intros READY ROW FRAME; rewrite affine_prepared_upper_math; apply memory_source_affine_iteration_value with
    (base:=entry_temps entry); [exact ROW| |].
  - intros identifier MEMBER; apply memory_source_affine_parameter_member in MEMBER as [READ OTHER].
    apply affine_prepared_words; [exact READY|apply affine_prepared_header_read; assumption].
  - eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER;
      apply memory_source_affine_parameter_member in MEMBER as [READ OTHER].
    apply in_or_app; right; apply affine_prepared_header_read; assumption.
Qed.

Lemma affine_prepared_upper_at_math entry i j :
  memory_source_affine_math (memory_affine_at_value row column i j (affine_prepared_valuation entry)) expression =
    affine_prepared_upper package entry i.
Proof.
  rewrite affine_prepared_upper_math.
  assert (EXT : forall e first second,
    (forall identifier, In identifier (memory_source_affine_reads e) -> first identifier = second identifier) ->
    memory_source_affine_math first e = memory_source_affine_math second e).
  { induction e; intros first second EQ; cbn [memory_source_affine_math];
      [apply EQ; cbn; auto|reflexivity| | | |].
    - rewrite IHe1 with (second:=second),IHe2 with (second:=second); try reflexivity;
        intros identifier MEMBER; apply EQ,in_or_app; auto.
    - rewrite IHe1 with (second:=second),IHe2 with (second:=second); try reflexivity;
        intros identifier MEMBER; apply EQ,in_or_app; auto.
    - rewrite IHe with (second:=second); [reflexivity|exact EQ].
    - rewrite IHe with (second:=second); [reflexivity|exact EQ]. }
  apply EXT; intros identifier READ; unfold memory_affine_at_value,memory_source_set_valuation.
  destruct (peq identifier row) as [SAME|OTHER]; [reflexivity|].
  destruct (peq identifier column) as [SAME|ANOTHER]; [|reflexivity].
  destruct (affine_prepared_context_protected (affine_prepared_header_read READ OTHER)) as [_ [FRESH REST]];
    contradiction.
Qed.

Lemma affine_prepared_point_values_at entry i j :
  map (memory_affine_at_value row column i j (affine_prepared_valuation entry))
    (memory_affine_inner_pointer_layout shape expression (affine_inner_pointer_body_parameters package)++
      affine_inner_pointer_scalars package) = affine_prepared_point_values package entry i j.
Proof.
  unfold memory_affine_inner_pointer_layout,affine_prepared_point_values;
    rewrite !map_app; cbn [map].
  fold row column.
  unfold memory_affine_at_value at 1 2.
  destruct (peq row row) as [|BAD]; [|contradiction].
  destruct (peq column row) as [SAME|OTHER]; [symmetry in SAME; exact (False_rect _ (affine_inner_pointer_rc CERT SAME))|].
  destruct (peq column column) as [|BAD]; [|contradiction].
  assert (SAME : forall identifiers, (forall identifier, In identifier identifiers -> In identifier context) ->
    map (memory_affine_at_value row column i j (affine_prepared_valuation entry)) identifiers =
    memory_source_parameter_values identifiers entry).
  { intros identifiers INCLUDED; unfold memory_source_parameter_values,affine_prepared_valuation.
    apply map_ext_in; intros identifier MEMBER.
    destruct (affine_prepared_context_protected (INCLUDED identifier MEMBER)) as [R [C K]].
    unfold memory_affine_at_value; destruct (peq identifier row);
      [contradiction|destruct (peq identifier column); [contradiction|reflexivity]]. }
  rewrite SAME by (intros identifier MEMBER; unfold context,memory_affine_inner_pointer_region_context;
    apply in_or_app; left; exact MEMBER).
  rewrite SAME by (intros identifier MEMBER; unfold context,memory_affine_inner_pointer_region_context;
    apply in_or_app; right; exact MEMBER).
  reflexivity.
Qed.
End STATE.

Print Assumptions affine_prepared_words.
Print Assumptions affine_prepared_count_range.
Print Assumptions affine_prepared_upper_range.
Print Assumptions affine_prepared_upper_value.
Print Assumptions affine_prepared_upper_at_math.
Print Assumptions affine_prepared_point_values_at.
