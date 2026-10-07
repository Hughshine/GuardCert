From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightNoWrap ClightRedundantSet ClightCountedLoop.
From GuardMemory Require Import GuardMemoryBooleanScan.
From GuardInterface Require Import ClightTensorWordOuter ClightTensorWordColumn ClightWordComponentScan
  ClightWordArithmeticTransport ClightWordCoordinateRename ClightRenamedWordObservation ClightDirectWordObservation
  ClightAffineJointObservation ClightObservedHeaderPrefix ClightNestedConstantSite ClightNestedConstantHeaders
  ClightLoadedOffsetHeader ClightSignedIndexedOffsetHeader ClightLoadedBoundSyntax
  ClightConstantBoundModel ClightNestedExpressionTransport ClightCheckPlanFrame.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Runtime syntax depends on address expressions, not on the ghost physical
    locations or values supplied by a receipt. *)
Theorem tensor_word_outer_same_addresses root_cache child_cache pointer row_cursor row_limit column_cursor column_limit
    component_cursor component_limit flag index upper rename first second :
  map word_observer_address first=map word_observer_address second ->
  tensor_word_outer_statement root_cache child_cache pointer row_cursor row_limit column_cursor column_limit
    component_cursor component_limit flag index upper rename first=
  tensor_word_outer_statement root_cache child_cache pointer row_cursor row_limit column_cursor column_limit
    component_cursor component_limit flag index upper rename second.
Proof.
  intro SAME; unfold tensor_word_outer_statement,tensor_word_outer_scan_code,tensor_word_column_code,
    tensor_word_column_component_code,word_component_scan_code,word_component_scan_loop,
    word_component_scan_body,renamed_word_check_code,renamed_word_observer_tree,direct_word_check_code.
  rewrite(@direct_word_observer_tree_addresses(fun _=>None)pointer(word_rename rename index)first second SAME); reflexivity.
Qed.

Definition tensor_word_header_scan shape pointer row_cursor row_limit column_cursor column_limit
    component_cursor component_limit flag index rename :=
  tensor_word_outer_statement(ncs_root_cache shape)(ncs_child_cache shape)pointer row_cursor row_limit
    column_cursor column_limit component_cursor component_limit flag index(ncs_upper shape)rename(ncs_observer_templates shape).

Lemma tensor_word_header_scan_receipt shape entry observers
    (receipt:ncs_observation_receipt shape entry observers)
    pointer row_cursor row_limit column_cursor column_limit component_cursor component_limit flag index rename :
  tensor_word_header_scan shape pointer row_cursor row_limit column_cursor column_limit
    component_cursor component_limit flag index rename=
  tensor_word_outer_statement(ncs_root_cache shape)(ncs_child_cache shape)pointer row_cursor row_limit
    column_cursor column_limit component_cursor component_limit flag index(ncs_upper shape)rename observers.
Proof.
  unfold tensor_word_header_scan; apply tensor_word_outer_same_addresses.
  symmetry; exact(ncs_receipt_addresses receipt).
Qed.

Lemma tensor_word_header_observer_scope shape entry observers
    (receipt:ncs_observation_receipt shape entry observers)live :
  In(ncs_pointer shape)live -> forall observer,In observer observers -> expression_scope live(word_observer_address observer).
Proof.
  intros POINTER observer MEMBER.
  assert(ADDRESS:In(word_observer_address observer)(map word_observer_address observers))by(apply in_map; exact MEMBER).
  rewrite(ncs_receipt_addresses receipt)in ADDRESS; cbn [ncs_observer_templates map word_observer_address]in ADDRESS.
  destruct ADDRESS as [SAME|[SAME|[]]]; rewrite <-SAME;
    change(incl[ncs_pointer shape]live); intros id [SAME'|[]]; subst id; exact POINTER.
Qed.

Section HEADERS.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable shape : nested_constant_shape.
Variable entry : clight_entry.
Variables pointer row_cursor row_limit column_cursor column_limit component_cursor component_limit flag : ident.
Variables index rhs : expr.
Variable rename : ident -> ident.
Variables stable live : list ident.
Variable observers : list clight_word_observer.
Variable receipt : ncs_observation_receipt shape entry observers.
Let row:=ncs_row shape.
Let column:=ncs_column shape.
Let iterator:=ncs_iterator shape.
Let root_cache:=ncs_root_cache shape.
Let child_cache:=ncs_child_cache shape.
Let helper:=ncs_component_helper shape.
Let upper:=ncs_upper shape.
Let root_count:=Int.signed(temp_word root_cache(entry_temps entry)).
Let child_count:=Int.signed(temp_word child_cache(entry_temps entry)).
Let inner_live:=row_cursor::row_limit::live.
Let component_live:=column_cursor::column_limit::inner_live.
Let component:=constant_body_source iterator(Int.repr upper)(ncs_leaf shape).
Definition tensor_word_header_result := @tensor_word_outer_result entry row column root_cache child_cache pointer
  row_cursor row_limit column_cursor column_limit component_cursor index upper rename observers.

(** Static source/resource laws belong to this language/domain adapter. A
    family factory must produce them from syntax and private-name checks. *)
Hypothesis LEAF : ncs_leaf shape=direct_word_store pointer index rhs.
Hypothesis WORD : word_arithmetic index.
Hypotheses (NONNEGATIVE : 0<=upper) (UPPER : signed_range upper).
Hypotheses (HELPER : In helper stable) (HELPER_WORD : (entry_temps entry)!helper=Some(Vint(Int.repr upper))).
Hypotheses (ROW_PRIVATE : ~In row stable) (COLUMN_PRIVATE : ~In column stable) (ITERATOR_PRIVATE : ~In iterator stable).
Hypotheses (ROW_COLUMN : row<>column) (ITERATOR_ROW : iterator<>row) (ITERATOR_COLUMN : iterator<>column).
Hypotheses (ROOT_STABLE : In root_cache stable) (CHILD_STABLE : In child_cache stable)
  (POINTER_STABLE : In pointer stable) (HEADER_STABLE : In(ncs_pointer shape)stable) (STABLE_LIVE : incl stable live).
Hypothesis SOURCE_SCOPE : incl(expression_temps index)(iterator::column::row::stable).
Hypotheses (RENAME_ITERATOR : rename iterator=component_cursor) (RENAME_COLUMN : rename column=column_cursor)
  (RENAME_ROW : rename row=row_cursor).
Hypothesis RENAME_STABLE : forall id,In id stable -> rename id=id.
Hypotheses (ROW_CURSOR_PRIVATE : ~In row_cursor live) (ROW_LIMIT_PRIVATE : ~In row_limit live)
  (COLUMN_CURSOR_PRIVATE : ~In column_cursor inner_live) (COLUMN_LIMIT_PRIVATE : ~In column_limit inner_live)
  (FLAG_PRIVATE : ~In flag inner_live) (COMPONENT_CURSOR_PRIVATE : ~In component_cursor component_live)
  (COMPONENT_LIMIT_PRIVATE : ~In component_limit component_live).
Hypotheses (ROW_CONTROLS : row_cursor<>row_limit) (ROW_CURSOR_FLAG : row_cursor<>flag) (ROW_LIMIT_FLAG : row_limit<>flag)
  (COLUMN_CONTROLS : column_cursor<>column_limit) (COLUMN_CURSOR_FLAG : column_cursor<>flag) (COLUMN_LIMIT_FLAG : column_limit<>flag)
  (COMPONENT_CONTROLS : component_cursor<>component_limit) (COMPONENT_CURSOR_FLAG : component_cursor<>flag)
  (COMPONENT_LIMIT_FLAG : component_limit<>flag).

(** Captured-header evaluation laws and point-observer scope are derived from
    the actual receipt. They are not optimizer-provided semantic callbacks. *)
Theorem tensor_word_header_scan_at_exit current after final :
  0<=root_count -> (0<root_count -> 0<=child_count) ->
  (entry_temps entry)!row=Some(Vint Int.zero) ->
  exec_stmt fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
    (ncs_original shape)E0 after final Out_normal ->
  check_plan_frameable(nested_cached_source row root_cache column child_cache component)=true ->
  incl(statement_temps(nested_cached_source row root_cache column child_cache component))live ->
  temp_agree live(entry_temps entry)current -> exists checked,
    exec_stmt fe(entry_ge entry)(entry_env entry)current(entry_memory entry)
      (tensor_word_header_scan shape pointer row_cursor row_limit column_cursor column_limit
        component_cursor component_limit flag index rename)E0 checked(entry_memory entry)Out_normal /\
    temp_agree live current checked /\ checked!flag=Some(memory_boolean_word tensor_word_header_result) /\
    (tensor_word_header_result=true -> exists exit,
      exec_stmt fe(entry_ge entry)(entry_env entry)checked(entry_memory entry)
        (nested_cached_source row root_cache column child_cache component)E0 exit final Out_normal /\
      temp_agree live after exit /\ header_observations_match(map word_observer_snapshot observers)final).
Proof.
  intros ROOT_RANGE CHILD_RANGE ROW SOURCE FRAMEABLE SCOPE FRAME.
  rewrite(@tensor_word_header_scan_receipt shape entry observers receipt pointer row_cursor row_limit
    column_cursor column_limit component_cursor component_limit flag index rename).
  unfold component in FRAMEABLE,SCOPE|-*; rewrite LEAF in FRAMEABLE,SCOPE|-*.
  unfold ncs_original in SOURCE; rewrite LEAF in SOURCE.
  unfold tensor_word_header_result.
  eapply(@tensor_word_outer_original_scan_at_exit fe entry iterator helper row column root_cache child_cache pointer
    row_cursor row_limit column_cursor column_limit component_cursor component_limit flag index rhs
    (signed_load_offset(ncs_pointer shape)(ncs_delta shape))
    (signed_indexed_offset(ncs_pointer shape)(ncs_index shape)(ncs_child_delta shape))
    upper rename stable live observers(fun _=>True))with(current:=current)(after:=after)(final:=final).
  all: try assumption; try reflexivity.
  - intros i temps memory _ RANGE COUNTER PUBLIC OBSERVED;
      eapply(@ncs_root_header_from_receipt shape entry observers receipt stable temps memory);
      [exact HEADER_STABLE|exact PUBLIC|exact OBSERVED].
  - intros i j temps memory ROWS COLUMNS ROW' COLUMN PUBLIC OBSERVED;
      eapply(@ncs_child_header_from_receipt shape entry observers receipt stable temps memory);
      [exact HEADER_STABLE|exact PUBLIC|exact OBSERVED].
  - intro ACTIVE; destruct(proj2(ncs_receipt_ready receipt))as [block [offset [raw [POINTER [READ CACHE]]]]].
    exists(Int.add raw(ncs_child_delta shape)); exact CACHE.
  - intro ACTIVE; exact(ncs_receipt_reads receipt).
  - apply tensor_word_header_observer_scope with(receipt:=receipt); apply STABLE_LIVE; exact HEADER_STABLE.
  - destruct(proj1(ncs_receipt_ready receipt))as [block [offset [raw [POINTER [READ CACHE]]]]].
    exists(Int.add raw(ncs_delta shape)); exact CACHE.
  - exact(ncs_receipt_initial receipt).
Qed.
End HEADERS.

Print Assumptions tensor_word_outer_same_addresses.
Print Assumptions tensor_word_header_scan_receipt.
Print Assumptions tensor_word_header_observer_scope.
Print Assumptions tensor_word_header_scan_at_exit.
