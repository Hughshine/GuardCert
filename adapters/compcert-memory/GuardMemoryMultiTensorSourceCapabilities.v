From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCountedLoop ClightTempFrame ClightPureExpr ClightStraightLine ClightFiniteRegion ClightNoWrap.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryFlatArrayBackend GuardMemoryPointerAccess
  GuardMemoryPointerSourceAccess GuardMemoryPointerCompute GuardMemoryPointerDefinedIndex GuardMemorySourceValueInterface GuardMemorySourceParameters
  GuardMemoryDynamicTensorLayout GuardMemoryDynamicTensorBackend GuardMemoryTensorSource GuardMemoryMultiTensorSource
  GuardMemoryMultiTensorSequence GuardMemoryRecursiveSource GuardMemoryRecursiveFirstLeaf.
From GuardInterface Require Import ClightQuietDeterminacy.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition multi_tensor_pointer_domain temps pointer := exists block base, temps!pointer = Some (Vptr block base).
Definition multi_tensor_word_domain temps identifier := exists word, temps!identifier = Some (Vint word).
Definition multi_tensor_operation_pointers dimensions layout source
    (operation : multi_tensor_source_operation dimensions layout source) :=
  map fst (mts_write operation :: mts_reads operation).
Definition multi_tensor_operation_capability dimensions layout source
    (operation : multi_tensor_source_operation dimensions layout source) temps :=
  Forall (multi_tensor_pointer_domain temps) (multi_tensor_operation_pointers operation) /\
  (forall identifier, In identifier (tensor_dimension_registers (tl dimensions)) -> multi_tensor_word_domain temps identifier) /\
  (forall identifier index, nth_error layout index = Some identifier ->
    In index (memory_source_parameter_positions (mts_value operation)) -> multi_tensor_word_domain temps identifier).

Lemma multi_tensor_source_read_has_base dimensions layout
    (access : multi_tensor_source_access dimensions layout) ge locals temps memory value :
  eval_expr ge locals temps memory (multi_tensor_source_lvalue access) value ->
  multi_tensor_pointer_domain temps (fst access).
Proof.
  intro RUN; unfold multi_tensor_source_lvalue in RUN; inversion RUN; subst.
  exists loc; eapply memory_pointer_lvalue_has_base; [apply tensor_source_access_type|eassumption].
Qed.

Lemma multi_tensor_source_reads_have_bases dimensions layout
    (accesses : list (multi_tensor_source_access dimensions layout)) ge locals temps memory loaded :
  Forall2 (fun code value => eval_expr ge locals temps memory code value) (map multi_tensor_source_lvalue accesses) loaded ->
  Forall (multi_tensor_pointer_domain temps) (map fst accesses).
Proof.
  revert loaded; induction accesses as [|access accesses IH]; intros loaded LOADS;
    cbn [map] in LOADS; inversion LOADS; subst; constructor.
  - eapply multi_tensor_source_read_has_base; eassumption.
  - eapply IH; eassumption.
Qed.

(** These observations come from the actual statement before mathematical
    layout/box checks. Each read is observed in this statement's own memory. *)
Theorem multi_tensor_source_operation_capability dimensions layout source
    (operation : multi_tensor_source_operation dimensions layout source) fe ge locals temps memory after final :
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  multi_tensor_operation_capability operation temps /\ after = temps.
Proof.
  intro RUN; rewrite (mts_exact operation) in RUN; unfold multi_tensor_source_lvalue in RUN; inversion RUN; subst after.
  assert (TYPE : typeof (mts_rhs operation) = type_int32s).
  { eapply memory_source_flat_type; [apply memory_pointer_register_types| |exact (mts_rhs_compile operation)].
    apply Forall_map,Forall_forall; intros; reflexivity. }
  match goal with CAST : sem_cast ?old _ _ _ = Some _ |- _ => rewrite TYPE in CAST;
    destruct old; cbn in CAST; try discriminate CAST; inversion CAST; subst end.
  assert (READ_TYPES : Forall (fun code => typeof code = type_int32s)
    (map multi_tensor_source_lvalue (mts_reads operation))).
  { apply Forall_map,Forall_forall; intros; reflexivity. }
  match goal with VALUE : eval_expr _ _ _ _ (mts_rhs operation) (Vint ?word) |- _ =>
    destruct (@memory_source_value_reads_exist ge locals temps memory (memory_pointer_register_codes layout)
      (map multi_tensor_source_lvalue (mts_reads operation)) (fun code value => eval_expr ge locals temps memory code value)
      (memory_pointer_register_types layout) READ_TYPES ltac:(intros; assumption)
      (mts_value operation) (mts_rhs operation) word (mts_reads_used operation) (mts_rhs_compile operation) VALUE)
      as [loaded LOADS]
  end.
  split; [|reflexivity]; split.
  - unfold multi_tensor_operation_pointers; cbn [map]; constructor.
    + exists loc; eapply memory_pointer_lvalue_has_base; [apply tensor_source_access_type|eassumption].
    + eapply multi_tensor_source_reads_have_bases; exact LOADS.
  - split.
    + eapply tensor_source_access_defined_dimensions; eassumption.
    + intros identifier index LOOKUP USED.
      eapply memory_source_used_register_typed;
        [exact READ_TYPES|exact LOOKUP|exact USED|exact (mts_rhs_compile operation)|eassumption].
Qed.

Theorem multi_tensor_source_tail_capabilities dimensions layout
    (items : list (multi_tensor_source_statement dimensions layout)) fe ge locals temps memory after final :
  tail_execution fe ge locals (map mt_statement items) temps memory after final ->
  Forall (fun item => multi_tensor_operation_capability (mt_operation item) temps) items /\ after = temps.
Proof.
  revert memory after final; induction items as [|item items IH]; intros memory after final RUN;
    cbn [map] in RUN; inversion RUN; subst.
  - split; [constructor|reflexivity].
  - match goal with POINT : exec_stmt _ _ _ _ _ (mt_statement item) _ _ _ _ |- _ =>
      destruct (@multi_tensor_source_operation_capability dimensions layout (mt_statement item) (mt_operation item)
        fe ge locals temps memory _ _ POINT) as [HEAD EXIT]; subst end.
    match goal with TAIL : tail_execution _ _ _ _ _ _ _ _ |- _ =>
      destruct (IH _ _ _ TAIL) as [REST EXIT] end.
    split; [constructor; assumption|exact EXIT].
Qed.

Theorem multi_tensor_source_body_capabilities dimensions layout body
    (items : list (multi_tensor_source_statement dimensions layout)) fe ge locals temps memory after final :
  flatten_region body = map mt_statement items ->
  exec_stmt fe ge locals temps memory body E0 after final Out_normal ->
  Forall (fun item => multi_tensor_operation_capability (mt_operation item) temps) items /\ after = temps.
Proof.
  intros BODY SOURCE; apply flatten_region_execution in SOURCE; rewrite BODY in SOURCE.
  eapply multi_tensor_source_tail_capabilities; exact SOURCE.
Qed.

Definition multi_tensor_body_pointers dimensions layout (items : list (multi_tensor_source_statement dimensions layout)) :=
  flat_map (fun item => multi_tensor_operation_pointers (mt_operation item)) items.
Definition multi_tensor_body_used_parameters dimensions layout (items : list (multi_tensor_source_statement dimensions layout)) :=
  flat_map (fun item => flat_map (fun index => match nth_error layout index with Some identifier => [identifier] | None => [] end)
    (memory_source_parameter_positions (mts_value (mt_operation item)))) items.
Definition multi_tensor_scalar_use_check dimensions layout scalars (items : list (multi_tensor_source_statement dimensions layout)) :=
  forallb (fun identifier => existsb (Pos.eqb identifier)
    (tensor_dimension_registers (tl dimensions) ++ multi_tensor_body_used_parameters items)) scalars.

Lemma multi_tensor_body_used_parameter_inverse dimensions layout
    (items : list (multi_tensor_source_statement dimensions layout)) identifier :
  In identifier (multi_tensor_body_used_parameters items) ->
  exists item index, In item items /\ nth_error layout index = Some identifier /\
    In index (memory_source_parameter_positions (mts_value (mt_operation item))).
Proof.
  intro USED; apply in_flat_map in USED as [item [MEMBER USED]].
  apply in_flat_map in USED as [index [POSITION LOOKUP]].
  destruct (nth_error layout index) as [id|] eqn:WORD; cbn in LOOKUP; [|contradiction].
  destruct LOOKUP as [<-|[]]; exists item,index; auto.
Qed.

(** An actually reached source leaf licenses entry pointer/word observations.
    No alias, dimension value, coordinate box or entry load value is assumed. *)
Theorem multi_tensor_source_region_first_capabilities dimensions nest scalars
    (items : list (multi_tensor_source_statement dimensions (memory_nest_iterators nest ++ scalars)))
    fe ge locals temps memory after final :
  flatten_region (memory_nest_leaf nest) = map mt_statement items -> items <> [] ->
  memory_nest_shapes nest -> memory_nest_fresh nest ->
  (forall identifier, In identifier (memory_nest_iterators nest) ->
    ~ In identifier (multi_tensor_body_pointers items ++ tensor_dimension_registers (tl dimensions) ++ scalars)) ->
  multi_tensor_scalar_use_check scalars items = true ->
  Forall (fun bound => 0 < Int.signed (temp_word bound temps)) (memory_nest_bounds nest) -> memory_nest_initial nest temps ->
  exec_stmt fe ge locals temps memory (memory_nest_source nest) E0 after final Out_normal ->
  Forall (multi_tensor_pointer_domain temps) (multi_tensor_body_pointers items) /\
  (forall identifier, In identifier (tensor_dimension_registers (tl dimensions) ++ scalars) -> multi_tensor_word_domain temps identifier).
Proof.
  intros BODY NONEMPTY SHAPES FRESH PROTECTED USED POSITIVE INITIAL SOURCE.
  destruct (@memory_recursive_first_leaf fe ge locals nest SHAPES FRESH
    (@multi_tensor_sequence_normal dimensions _ items _ BODY) (@multi_tensor_sequence_quiet dimensions _ items _ BODY)
    (@multi_tensor_sequence_writes dimensions _ items _ BODY)
    (multi_tensor_body_pointers items ++ tensor_dimension_registers (tl dimensions) ++ scalars)
    temps memory after final PROTECTED POSITIVE INITIAL SOURCE)
    as [leaf_temps [leaf_after [leaf_final [FRAME LEAF]]]].
  destruct (@multi_tensor_source_body_capabilities dimensions _ (memory_nest_leaf nest) items
    fe ge locals leaf_temps memory leaf_after leaf_final BODY LEAF) as [CAPABILITIES _].
  assert (POINTERS : Forall (multi_tensor_pointer_domain leaf_temps) (multi_tensor_body_pointers items)).
  { apply Forall_forall; intros pointer MEMBER; apply in_flat_map in MEMBER as [item [ITEM POINTER]].
    apply Forall_forall with (x := item) in CAPABILITIES; [|exact ITEM].
    destruct CAPABILITIES as [POINTERS _]; apply Forall_forall with (x := pointer) in POINTERS; assumption. }
  assert (DIMENSIONS : forall identifier, In identifier (tensor_dimension_registers (tl dimensions)) -> multi_tensor_word_domain leaf_temps identifier).
  { destruct items as [|item items]; [contradiction|].
    inversion CAPABILITIES as [|same tail [_ [DIMENSIONS _]] REST]; subst; exact DIMENSIONS. }
  split.
  - apply Forall_forall; intros pointer MEMBER; apply Forall_forall with (x := pointer) in POINTERS; [|exact MEMBER].
    destruct POINTERS as [block [base POINTER]]; exists block,base; rewrite <- FRAME; [exact POINTER|apply in_or_app; left; exact MEMBER].
  - intros identifier MEMBER; assert (WORD : multi_tensor_word_domain leaf_temps identifier).
    { apply in_app_or in MEMBER as [DIMENSION|SCALAR]; [apply DIMENSIONS; exact DIMENSION|].
      unfold multi_tensor_scalar_use_check in USED; apply forallb_forall with (x := identifier) in USED; [|exact SCALAR].
      apply existsb_exists in USED as [id [USED SAME]]; apply Pos.eqb_eq in SAME; subst id.
      apply in_app_or in USED as [DIMENSION|PARAMETER]; [apply DIMENSIONS; exact DIMENSION|].
      apply multi_tensor_body_used_parameter_inverse in PARAMETER as [item [index [ITEM [LOOKUP POSITION]]]].
      apply Forall_forall with (x := item) in CAPABILITIES; [|exact ITEM].
      destruct CAPABILITIES as [_ [_ PARAMETERS]]; eapply PARAMETERS; eassumption. }
    destruct WORD as [word WORD]; exists word; rewrite <- FRAME; [exact WORD|apply in_or_app; right; exact MEMBER].
Qed.

Print Assumptions multi_tensor_source_read_has_base.
Print Assumptions multi_tensor_source_reads_have_bases.
Print Assumptions multi_tensor_source_operation_capability.
Print Assumptions multi_tensor_source_tail_capabilities.
Print Assumptions multi_tensor_source_body_capabilities.
Print Assumptions multi_tensor_body_used_parameter_inverse.
Print Assumptions multi_tensor_source_region_first_capabilities.
