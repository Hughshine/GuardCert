From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Integers.
From compcert.common Require Import AST Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightSyntaxEquality ClightStraightLine ClightRectangularLoops
  ClightNoWrap ClightRedundantSet ClightCountedLoop ClightCondition ClightTempFrame ClightRegionProgress ClightStructuredProgress.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryAffineSourceExpressions
  GuardMemoryRecursiveSource GuardMemorySourceParameters GuardMemoryDynamicTensorBackend GuardMemoryTensorSource.
From GuardInterface Require Import ClightTensorCompleteGuard ClightTensorBoxGuard ClightLoopAdministrative.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The proposer returns data only. Every source equality and static condition
    below is checked again before constructing the dependent package. *)
Record tensor_region_description := TensorRegionDescription {
  tensor_region_dimensions : list tensor_dimension_source;
  tensor_region_scalars : list ident;
  tensor_region_pointer : ident;
  tensor_region_array : ident;
  tensor_region_write : list memory_source_affine;
  tensor_region_reads : list(list memory_source_affine);
  tensor_region_value : value_expression;
  tensor_region_cap : Z;
  tensor_region_profile : list(Z*Z)
}.

Fixpoint tensor_propose_nest fuel source : option memory_source_nest :=
  match fuel with
  | O=>None
  | S rest=>match checked_structured_loop source with
    | Some loop=>if described_frontend loop then
        match flatten_region(described_body loop)with
        | [reset;next]=>match tensor_propose_nest rest next with
          | Some child=>Some(MemorySourceAxis(described_iterator loop)(described_bound loop)(described_body loop)child)
          | None=>None end
        | _=>Some(MemorySourceAxis(described_iterator loop)(described_bound loop)(described_body loop)
            (MemorySourceLeaf(described_body loop)))end
      else None
    | None=>Some(MemorySourceLeaf source)end end.

Definition tensor_member identifier identifiers := existsb(Pos.eqb identifier)identifiers.
Lemma tensor_member_true identifier identifiers : tensor_member identifier identifiers=true <-> In identifier identifiers.
Proof.
  unfold tensor_member; rewrite existsb_exists; split.
  - intros [actual [MEMBER SAME]]; apply Pos.eqb_eq in SAME; subst; exact MEMBER.
  - intro MEMBER; exists identifier; split; [exact MEMBER|apply Pos.eqb_refl].
Qed.
Definition tensor_disjoint first second := forallb(fun identifier=>negb(tensor_member identifier second))first.
Fixpoint tensor_unique identifiers := match identifiers with
  | []=>true|identifier::rest=>negb(tensor_member identifier rest)&&tensor_unique rest end.
Lemma tensor_unique_sound identifiers : tensor_unique identifiers=true -> NoDup identifiers.
Proof.
  induction identifiers as [|identifier identifiers IH]; cbn; [intro; constructor|].
  rewrite andb_true_iff; intros [FRESH UNIQUE]; constructor; [|apply IH; exact UNIQUE].
  intro MEMBER; apply tensor_member_true in MEMBER; rewrite MEMBER in FRESH; discriminate.
Qed.
Lemma tensor_disjoint_sound first second : tensor_disjoint first second=true ->
  forall identifier,In identifier first -> ~In identifier second.
Proof.
  intros CHECK identifier MEMBER BOTH; unfold tensor_disjoint in CHECK.
  apply forallb_forall with(x:=identifier)in CHECK; [|exact MEMBER].
  apply tensor_member_true in BOTH; rewrite BOTH in CHECK; discriminate.
Qed.
Definition tensor_subset first second := forallb(fun identifier=>tensor_member identifier second)first.
Lemma tensor_subset_sound first second : tensor_subset first second=true ->
  forall identifier,In identifier first -> In identifier second.
Proof.
  intros CHECK identifier MEMBER; apply tensor_member_true.
  apply forallb_forall with(x:=identifier)in CHECK; assumption.
Qed.

Fixpoint tensor_nest_shapes_dec nest : {memory_nest_shapes nest}+{~memory_nest_shapes nest}.
Proof.
  destruct nest as [code|iterator bound body child]; [left; exact I|].
  destruct(tensor_nest_shapes_dec child)as [SHAPES|BAD]; [|right; intros [_ SHAPES]; contradiction].
  destruct child as [code|inner limit inner_body rest].
  - destruct(statement_eq body code)as [SAME|BAD]; [left; split; assumption|right; intros [SAME _]; contradiction].
  - destruct(list_eq_dec statement_eq(flatten_region body)
      [rectangle_reset inner;memory_nest_source(MemorySourceAxis inner limit inner_body rest)])as [SAME|BAD];
      [left; split; assumption|right; intros [SAME _]; contradiction].
Defined.

Definition tensor_position_member layout positions identifier := existsb(fun index=>
  match nth_error layout index with Some actual=>Pos.eqb identifier actual|None=>false end)positions.
Lemma tensor_position_member_sound layout positions identifier : tensor_position_member layout positions identifier=true ->
  exists index,nth_error layout index=Some identifier /\ In index positions.
Proof.
  unfold tensor_position_member; rewrite existsb_exists; intros [index [MEMBER VALUE]].
  destruct(nth_error layout index)as [actual|]eqn:LOOKUP; [|discriminate].
  apply Pos.eqb_eq in VALUE; subst; exists index; split; assumption.
Qed.
Definition tensor_region_used_check dimensions nest scalars value := forallb(fun identifier=>
  tensor_member identifier(tensor_dimension_registers(tl dimensions)) ||
  tensor_position_member(memory_nest_iterators nest++scalars)(memory_source_parameter_positions value)identifier)scalars.
Lemma tensor_region_used_sound dimensions nest scalars value : tensor_region_used_check dimensions nest scalars value=true ->
  forall identifier,In identifier scalars -> In identifier(tensor_dimension_registers(tl dimensions)) \/
    exists index,nth_error(memory_nest_iterators nest++scalars)index=Some identifier /\
      In index(memory_source_parameter_positions value).
Proof.
  intros CHECK identifier MEMBER; apply forallb_forall with(x:=identifier)in CHECK; [|exact MEMBER].
  apply orb_true_iff in CHECK as [DIMENSION|PARAMETER];
    [left; apply tensor_member_true; exact DIMENSION|right; apply tensor_position_member_sound; exact PARAMETER].
Qed.

Fixpoint describe_tensor_region_reads dimensions layout coordinates : option(list(tensor_source_access dimensions layout)) :=
  match coordinates with
  | []=>Some []
  | head::rest=>match describe_tensor_source_access dimensions layout head,describe_tensor_region_reads dimensions layout rest with
    | Some access,Some accesses=>Some(access::accesses)|_,_=>None end end.

Record tensor_region_package(source:statement) := TensorRegionPackage {
  tensor_description : tensor_region_description;
  tensor_nest : memory_source_nest;
  tensor_region_source : trim_loop_skips source=memory_nest_source tensor_nest;
  tensor_operation : tensor_source_operation(tensor_region_dimensions tensor_description)
    (memory_nest_iterators tensor_nest++tensor_region_scalars tensor_description)
    (tensor_region_pointer tensor_description)(tensor_region_array tensor_description)(memory_nest_leaf tensor_nest);
  tensor_region_shapes : memory_nest_shapes tensor_nest;
  tensor_region_fresh : memory_nest_fresh tensor_nest;
  tensor_region_unique : NoDup(memory_nest_iterators tensor_nest++tensor_region_scalars tensor_description);
  tensor_region_protected : forall identifier,In identifier(memory_nest_iterators tensor_nest) ->
    ~In identifier(tensor_region_pointer tensor_description::tensor_dimension_registers(tensor_region_dimensions tensor_description)
      ++tensor_region_scalars tensor_description);
  tensor_region_used : forall identifier,In identifier(tensor_region_scalars tensor_description) ->
    In identifier(tensor_dimension_registers(tl(tensor_region_dimensions tensor_description))) \/
    exists index,nth_error(memory_nest_iterators tensor_nest++tensor_region_scalars tensor_description)index=Some identifier /\
      In index(memory_source_parameter_positions(tensor_source_value tensor_operation));
  tensor_region_dimension_reads : forall identifier,In identifier(tensor_dimension_registers(tensor_region_dimensions tensor_description)) ->
    In identifier(memory_nest_bounds tensor_nest) \/ In identifier(tensor_dimension_registers(tl(tensor_region_dimensions tensor_description)));
  tensor_region_signed_cap : signed_range(tensor_region_cap tensor_description);
  tensor_region_box_tree : decision_tree;
  tensor_region_box_compile : compile_tensor_box_guard
    (tensor_coordinate_layout(tensor_region_dimensions tensor_description)tensor_nest(tensor_region_scalars tensor_description))
    (tensor_region_profile tensor_description)(memory_nest_bounds tensor_nest)(tensor_region_scalars tensor_description)
    (tensor_region_dimensions tensor_description)(tensor_operation_accesses tensor_operation)=Some tensor_region_box_tree
}.

Definition check_tensor_region_description source(description:tensor_region_description) : option(tensor_region_package source).
Proof.
  destruct(tensor_propose_nest(progress_syntax_size(trim_loop_skips source))(trim_loop_skips source))as [nest|]; [|exact None].
  destruct(memory_nest_iterators nest)eqn:NONEMPTY; [exact None|].
  destruct(statement_eq(trim_loop_skips source)(memory_nest_source nest))as [SOURCE|]; [|exact None].
  destruct(tensor_nest_shapes_dec nest)as [SHAPES|]; [|exact None].
  destruct(tensor_unique(memory_nest_iterators nest++tensor_region_scalars description))eqn:UNIQUE_CHECK; [|exact None].
  pose proof(tensor_unique_sound(memory_nest_iterators nest++tensor_region_scalars description)UNIQUE_CHECK)as UNIQUE.
  destruct(tensor_disjoint(memory_nest_iterators nest)(memory_nest_bounds nest))eqn:FRESH; [|exact None].
  destruct(tensor_disjoint(memory_nest_iterators nest)(tensor_region_pointer description::
    tensor_dimension_registers(tensor_region_dimensions description)++tensor_region_scalars description))eqn:PROTECTED; [|exact None].
  destruct(describe_tensor_source_access(tensor_region_dimensions description)
    (memory_nest_iterators nest++tensor_region_scalars description)(tensor_region_write description))as [write|]; [|exact None].
  destruct(describe_tensor_region_reads(tensor_region_dimensions description)
    (memory_nest_iterators nest++tensor_region_scalars description)(tensor_region_reads description))as [reads|]; [|exact None].
  destruct(check_tensor_source_operation(tensor_region_pointer description)(tensor_region_array description)
    (memory_nest_leaf nest)write reads(tensor_region_value description))as [operation|]; [|exact None].
  destruct(tensor_region_used_check(tensor_region_dimensions description)nest(tensor_region_scalars description)
    (tensor_source_value operation))eqn:USED; [|exact None].
  destruct(tensor_subset(tensor_dimension_registers(tensor_region_dimensions description))
    (memory_nest_bounds nest++tensor_dimension_registers(tl(tensor_region_dimensions description))))eqn:DIMENSIONS; [|exact None].
  destruct(Z_le_dec Int.min_signed(tensor_region_cap description))as [LOW|]; [|exact None].
  destruct(Z_le_dec(tensor_region_cap description)Int.max_signed)as [HIGH|]; [|exact None].
  destruct(compile_tensor_box_guard(tensor_coordinate_layout(tensor_region_dimensions description)nest(tensor_region_scalars description))
    (tensor_region_profile description)(memory_nest_bounds nest)(tensor_region_scalars description)
    (tensor_region_dimensions description)(tensor_operation_accesses operation))as [tree|]eqn:COMPILE; [|exact None].
  refine(Some {|tensor_description:=description;tensor_nest:=nest;tensor_region_source:=SOURCE;tensor_operation:=operation;
    tensor_region_shapes:=SHAPES;tensor_region_unique:=UNIQUE;tensor_region_box_tree:=tree;tensor_region_box_compile:=COMPILE|}).
  - split; [exact(@NoDup_app_remove_r _ (memory_nest_iterators nest)(tensor_region_scalars description)UNIQUE)|
      apply tensor_disjoint_sound; exact FRESH].
  - apply tensor_disjoint_sound; exact PROTECTED.
  - apply tensor_region_used_sound; exact USED.
  - intros identifier MEMBER; apply in_app_or; eapply tensor_subset_sound; [exact DIMENSIONS|exact MEMBER].
  - split; assumption.
Defined.

Lemma tensor_region_source_execution source(package:tensor_region_package source) fe ge locals le memory trace after final outcome :
  exec_stmt fe ge locals le memory source trace after final outcome ->
  exec_stmt fe ge locals le memory(memory_nest_source(tensor_nest package))trace after final outcome.
Proof. rewrite <-(tensor_region_source package); apply(proj2(trim_loop_skips_equivalent fe source ge locals le memory trace after final outcome)). Qed.
Lemma tensor_region_source_writes source(package:tensor_region_package source) :
  writes_only(memory_nest_iterators(tensor_nest package))source.
Proof. apply trim_loop_skips_writes; rewrite(tensor_region_source package); apply memory_nest_source_writes;
  [apply tensor_region_shapes|exact(tensor_source_operation_writes(tensor_operation package))]. Qed.
Lemma tensor_region_source_quiet source(package:tensor_region_package source) : quiet_statement source=true.
Proof. rewrite <-(trim_loop_skips_quiet source); rewrite(tensor_region_source package); apply memory_nest_source_quiet;
  [apply tensor_region_shapes|exact(tensor_source_operation_quiet(tensor_operation package))]. Qed.
Print Assumptions tensor_member_true.
Print Assumptions tensor_disjoint_sound.
Print Assumptions tensor_unique_sound.
Print Assumptions tensor_subset_sound.
Print Assumptions tensor_nest_shapes_dec.
Print Assumptions tensor_region_used_sound.
Print Assumptions check_tensor_region_description.
Print Assumptions tensor_region_source_execution.
Print Assumptions tensor_region_source_writes.
Print Assumptions tensor_region_source_quiet.
