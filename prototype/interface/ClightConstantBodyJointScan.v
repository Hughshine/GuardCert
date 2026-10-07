From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightLoopSyntax
  ClightRegionProgress ClightNoWrap CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops GuardMemoryWindowCells GuardMemoryBooleanScan
  GuardMemoryNaryCompute GuardMemoryNaryAffineAccess GuardMemoryNaryAffineExpressions GuardMemoryWindowCompute
  GuardMemoryWindowAccess GuardMemoryFootprintCapabilities GuardMemoryFiniteAliasCondition
  GuardMemoryAffineSourceExpressions GuardMemoryObservationStability.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestValuation AffineNestMathDomain
  AffineNestSourceDecode AffineNestLeafModel AffineNestLeafDecode AffineNestLoopEncoding AffineNestScanModel
  AffineNestScanPoints AffineNestScanSyntax AffineNestScanAddress AffineNestScanAccesses AffineNestScanExecution
  AffineNestWriteFootprint.
From GuardInterface Require Import ClightConstantBoundModel ClightConstantBodyCapabilities
  ClightAffineJointObservation ClightObservedWordProbe ClightObservedHeaderPrefix ClightStorePermissions
  ClightStructuredStorePermissions ClightExpressionBodyPrefix.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Theorem constant_affine_prefix_writes_preserve iterator helper upper body child coordinates prefix parameters bounds
  window_lower window_upper pointers operations
  (certificate:affine_leaf_certificate(affine_nest_leaf child) bounds window_lower window_upper
    (coordinates++parameters) [] pointers operations)
  fe ge locals initial valuation code temps memory after final written observation :
  let nest:=AffineSourceAxis iterator helper(MemorySourceConstant upper) body child in
  coordinates=prefix++affine_nest_iterators nest -> affine_nest_shapes nest -> NoDup(affine_nest_controls nest) ->
  affine_nest_bound_dependencies prefix parameters nest ->
  (forall identifier,In identifier((prefix++parameters)++pointers)->~In identifier(affine_nest_mutated nest)) ->
  affine_math_domain bounds(coordinates++parameters) nest valuation 0 ->
  affine_word_view(prefix++parameters) valuation temps -> temp_agree pointers initial temps ->
  writes_only written body -> ~In helper written -> temps!helper=Some(Vint(Int.repr upper)) ->
  affine_lower_nest nest prefix parameters(L.Constant 0)(affine_checked_leaf_code coordinates parameters [] operations)=Some code ->
  exec_stmt fe ge locals temps memory(constant_body_source iterator(Int.repr upper) body) E0 after final Out_normal ->
  (forall point,affine_scan_point nest valuation 0 point -> forall operation,In operation operations ->
    forall write,window_multi_pointer_locations initial window_lower window_upper
      (affine_scan_access_cell point(memory_nary_compute_write operation))=Some write -> location_disjoint write observation) ->
  location_load observation final=location_load observation memory.
Proof.
  cbn zeta; intros COORDINATES SHAPES FRESH DEPENDENCIES PROTECTED DOMAIN WORDS POINTERS WRITES PRIVATE HELPER LOWER SOURCE APART.
  pose proof(@constant_affine_prefix_body_decode iterator helper upper body child coordinates prefix parameters bounds
    window_lower window_upper pointers operations certificate fe ge locals initial valuation code temps memory after final []
    written COORDINATES SHAPES FRESH DEPENDENCIES PROTECTED DOMAIN WORDS POINTERS WRITES PRIVATE HELPER LOWER SOURCE) as MODEL.
  eapply memory_loop_observation_preserved; [|exact MODEL].
  unfold affine_checked_leaf_code in LOWER; rewrite app_nil_r in LOWER.
  pose proof(affine_leaf_unique certificate) as UNIQUE; rewrite app_nil_r in UNIQUE.
  eapply affine_scan_checked_writes_apart with(prefix:=prefix)(lower_code:=L.Constant 0)(bounds:=bounds)
    (window_lower:=window_lower)(window_upper:=window_upper); try eassumption; try reflexivity.
  exact(affine_leaf_valid certificate).
Qed.

(** The scan consumes a reached ORIGINAL constant subbody. Its enclosing
    coordinate prefix may contain both loaded-loop coordinates. Neither
    enclosing cached execution nor observation stability licenses this scan. *)
Section BODY.
Variables iterator helper : ident.
Variable upper : Z.
Variable body : statement.
Variable child : affine_source_nest.
Variables coordinates prefix parameters : list ident.
Variable bounds : list(Z*Z).
Variables window_lower window_upper : Z.
Variables pointers : list ident.
Variable operations : list memory_nary_compute.
Variable certificate : affine_leaf_certificate(affine_nest_leaf child) bounds window_lower window_upper
  (coordinates++parameters) [] pointers operations.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variables initial temps after : temp_env.
Variables guard_memory memory final : mem.
Variable valuation : ident->Z.
Variable code : L.stmt.
Variable written : list ident.
Let nest:=AffineSourceAxis iterator helper(MemorySourceConstant upper) body child.
Let locations:=window_multi_pointer_locations initial window_lower window_upper.
Hypothesis COORDINATES : coordinates=prefix++affine_nest_iterators nest.
Hypothesis SHAPES : affine_nest_shapes nest.
Hypothesis FRESH : NoDup(affine_nest_controls nest).
Hypothesis DEPENDENCIES : affine_nest_bound_dependencies prefix parameters nest.
Hypothesis PROTECTED : forall identifier, In identifier((prefix++parameters)++pointers) -> ~In identifier(affine_nest_mutated nest).
Hypothesis DOMAIN : affine_math_domain bounds(coordinates++parameters) nest valuation 0.
Hypothesis WORDS : affine_word_view(prefix++parameters) valuation temps.
Hypothesis POINTERS : temp_agree pointers initial temps.
Hypothesis WRITES : writes_only written body.
Hypothesis PRIVATE : ~In helper written.
Hypothesis HELPER : temps!helper=Some(Vint(Int.repr upper)).
Hypothesis LOWER : affine_lower_nest nest prefix parameters(L.Constant 0)
  (affine_checked_leaf_code coordinates parameters [] operations)=Some code.
Hypothesis BACK : memory_accesses_back guard_memory memory.
Hypothesis SOURCE : exec_stmt fe ge locals temps memory(constant_body_source iterator(Int.repr upper) body)
  E0 after final Out_normal.

Lemma constant_body_scan_point_capable point operation :
  affine_scan_point nest valuation 0 point -> In operation operations ->
  memory_cell_capable locations guard_memory(affine_scan_access_cell point(memory_nary_compute_write operation)).
Proof.
  intros POINT OPERATION.
  pose proof(@constant_affine_prefix_body_capabilities iterator helper upper body child coordinates prefix parameters bounds
    window_lower window_upper pointers operations certificate fe ge locals initial valuation code temps guard_memory memory
    after final written COORDINATES SHAPES FRESH DEPENDENCIES PROTECTED DOMAIN WORDS POINTERS WRITES PRIVATE HELPER LOWER
    BACK SOURCE point POINT) as CAPABLE.
  rewrite(@affine_scan_point_footprint _ _ _ _ [] _ point(affine_leaf_valid certificate)) in CAPABLE.
  apply Forall_forall with(x:=affine_scan_access_cell point(memory_nary_compute_write operation)) in CAPABLE;
    [exact CAPABLE|apply in_map].
  unfold affine_scan_accesses; apply in_flat_map; exists operation; split; [exact OPERATION|cbn; auto].
Qed.

Lemma constant_body_scan_write_binding point operation values current :
  affine_scan_point nest valuation 0 point -> In operation operations -> temp_agree pointers initial current ->
  affine_scan_word_view(coordinates++parameters) values point current ->
  memory_cell_address_binding(fun _=>affine_scan_address(memory_nary_access_array(memory_nary_compute_write operation)) values
    (memory_nary_access_expression(memory_nary_compute_write operation))) locations(Entry ge locals current guard_memory)
    (affine_scan_access_cell point(memory_nary_compute_write operation)).
Proof.
  intros POINT OPERATION FRAME SCAN_WORDS.
  pose proof(affine_leaf_valid certificate) as VALID; apply Forall_forall with(x:=operation) in VALID; [|exact OPERATION].
  destruct VALID as [[LOW [HIGH [ENCODE RANGE]]] REST].
  pose proof(affine_leaf_covered certificate) as COVERED; apply Forall_forall with(x:=operation) in COVERED; [|exact OPERATION].
  destruct COVERED as [OWNED REST_COVERED].
  eapply affine_scan_address_binding;
    [exact LOW|exact HIGH|apply FRAME; exact OWNED| |apply constant_body_scan_point_capable; assumption].
  intros identifier MEMBER; apply SCAN_WORDS.
  eapply memory_encode_nary_index_reads; eassumption.
Qed.

Variables observers : list clight_word_observer.
Variable public : list ident.
Hypothesis POINTER_SCOPE : incl pointers public.
Hypothesis OBSERVERS : forall observer, In observer observers -> word_observer_receipt ge locals initial guard_memory observer.
Hypothesis OBSERVER_SCOPE : forall observer, In observer observers -> expression_scope public(word_observer_address observer).

Lemma constant_body_joint_point_test point operation observer values current :
  affine_scan_point nest valuation 0 point -> In operation operations -> In observer observers ->
  temp_agree public initial current -> affine_scan_word_view(coordinates++parameters) values point current ->
  expression_test(affine_joint_comparison_test values(observer,operation))(Entry ge locals current guard_memory)
    (affine_joint_comparison_result locations point(observer,operation)).
Proof.
  intros POINT OPERATION OBSERVER FRAME SCAN_WORDS.
  unfold affine_joint_comparison_test,affine_joint_comparison_result; cbn [fst snd].
  eapply (@observed_word_expression_check_evaluation
    (fun _=>affine_scan_address(memory_nary_access_array(memory_nary_compute_write operation)) values
      (memory_nary_access_expression(memory_nary_compute_write operation)))
    locations(affine_scan_access_cell point(memory_nary_compute_write operation)) ge locals current guard_memory observer);
    [apply constant_body_scan_write_binding; [exact POINT|exact OPERATION| |exact SCAN_WORDS]|].
  - eapply temp_agree_weaken; eassumption.
  - eapply word_observer_receipt_frame; [apply OBSERVERS|apply OBSERVER_SCOPE|exact FRAME]; exact OBSERVER.
Qed.

Theorem constant_body_joint_leaf_execution point values flag protected current good :
  affine_scan_point nest valuation 0 point ->
  ~In flag protected -> ~In flag public -> ~In flag(map values(coordinates++parameters)) ->
  temp_agree public initial current -> affine_scan_word_view(coordinates++parameters) values point current ->
  current!flag=Some(memory_boolean_word good) ->
  exists checked,
    exec_stmt fe ge locals current guard_memory(affine_joint_observation_leaf observers operations values flag)
      E0 checked guard_memory Out_normal /\ temp_agree protected current checked /\
    checked!flag=Some(memory_boolean_word(good&&affine_joint_observation_result locations observers operations point)).
Proof.
  intros POINT FLAG_PROTECTED FLAG_PUBLIC FLAG_WORD FRAME SCAN_WORDS FLAG.
  unfold affine_joint_observation_leaf,affine_joint_observation_result.
  eapply affine_joint_comparison_execution with(public:=public)(base:=initial)
    (layout:=coordinates++parameters)(point:=point)(locations:=locations); try eassumption.
  intros [observer operation] inside MEMBER INSIDE_FRAME INSIDE_WORDS.
  apply affine_joint_comparisons_member in MEMBER as [OBSERVER OPERATION].
  eapply constant_body_joint_point_test; eassumption.
Qed.

(** This is an actual recursive Clight scan. The leaf callback required by
    the old scan library is discharged above from source execution, checked
    leaf metadata, and actual observation receipts, rather than postulated. *)
Theorem constant_body_joint_scan_execution controls values flag live current good :
  NoDup(map controls(affine_nest_controls nest)) ->
  (forall identifier,In identifier(affine_nest_iterators nest)->values identifier=controls identifier) ->
  (forall identifier,In identifier(affine_nest_controls nest)->~In(controls identifier) live /\ controls identifier<>flag) ->
  ~In flag live -> ~In flag public -> ~In flag(map values(coordinates++parameters)) ->
  incl public live -> incl(map values(prefix++parameters)) live ->
  affine_scan_word_view(prefix++parameters) values valuation current -> temp_agree public initial current ->
  current!flag=Some(memory_boolean_word good) ->
  exists checked,
    exec_stmt fe ge locals current guard_memory
      (affine_scan_statement nest controls values(Econst_int Int.zero type_int32s)
        (affine_joint_observation_leaf observers operations values flag)) E0 checked guard_memory Out_normal /\
    temp_agree live current checked /\ checked!flag=Some(memory_boolean_word(good&&
      affine_scan_result nest valuation 0(affine_joint_observation_result locations observers operations))).
Proof.
  intros UNIQUE VALUES CONTROL_PRIVATE FLAG_LIVE FLAG_PUBLIC FLAG_WORD PUBLIC_LIVE PREFIX_LIVE SCAN_WORDS FRAME FLAG.
  eapply affine_scan_execution with(prefix:=prefix)(parameters:=parameters)(valuation:=valuation)(lower:=0)
    (public:=public)(base:=initial)(bounds:=bounds)(layout:=coordinates++parameters);
    try eassumption; try reflexivity.
  - constructor.
  - intros point inside before protected POINT INSIDE_WORDS INSIDE_FRAME BEFORE PROTECTED_FLAG INCLUDED.
    rewrite <-COORDINATES in INSIDE_WORDS.
    eapply constant_body_joint_leaf_execution; eassumption.
Qed.

Theorem constant_body_joint_scan_writes_apart observer :
  In observer observers ->
  affine_scan_result nest valuation 0(affine_joint_observation_result locations observers operations)=true ->
  forall point, affine_scan_point nest valuation 0 point -> forall operation, In operation operations ->
  forall write, locations(affine_scan_access_cell point(memory_nary_compute_write operation))=Some write ->
    location_disjoint write(word_observer_location observer).
Proof.
  intros OBSERVER CHECK point POINT operation OPERATION write WRITE.
  pose proof(proj1(@affine_scan_result_points nest valuation 0 _) CHECK point POINT) as POINT_CHECK.
  unfold affine_joint_observation_result in POINT_CHECK.
  apply forallb_forall with(x:=(observer,operation)) in POINT_CHECK;
    [|apply affine_joint_comparisons_member; auto].
  unfold affine_joint_comparison_result in POINT_CHECK; cbn [fst snd] in POINT_CHECK.
  destruct(@word_observer_receipt_load ge locals initial guard_memory observer(OBSERVERS observer OBSERVER)) as [READ ALIGN].
  eapply observed_word_cell_check_sound;
    [apply constant_body_scan_point_capable; eassumption|exact WRITE|reflexivity|exact ALIGN|exact POINT_CHECK].
Qed.

Theorem constant_body_joint_scan_preserves_observation observer :
  In observer observers ->
  affine_scan_result nest valuation 0(affine_joint_observation_result locations observers operations)=true ->
  location_load(word_observer_location observer) final=location_load(word_observer_location observer) memory.
Proof.
  intros OBSERVER CHECK.
  eapply constant_affine_prefix_writes_preserve with(certificate:=certificate); try eassumption.
  exact(constant_body_joint_scan_writes_apart observer OBSERVER CHECK).
Qed.

Theorem constant_body_joint_scan_preserves_snapshots :
  affine_scan_result nest valuation 0(affine_joint_observation_result locations observers operations)=true ->
  header_observations_match(map word_observer_snapshot observers) memory ->
  header_observations_match(map word_observer_snapshot observers) final.
Proof.
  intros CHECK MATCH; unfold header_observations_match in *.
  apply Forall_forall; intros snapshot MEMBER; apply in_map_iff in MEMBER as [observer [<- OBSERVER]].
  cbn [word_observer_snapshot fst snd]; rewrite(constant_body_joint_scan_preserves_observation observer OBSERVER CHECK).
  apply Forall_forall with(x:=word_observer_snapshot observer) in MATCH;
    [exact MATCH|apply in_map; exact OBSERVER].
Qed.

(** The reached execution licenses the check. Acceptance then protects ALL
    actual subbody executions with the same coordinate/parameter view and
    pointer bindings. Their memory need not be the original guard memory. *)
Theorem constant_body_joint_scan_preserves_all_sources current before exit last :
  affine_scan_result nest valuation 0(affine_joint_observation_result locations observers operations)=true ->
  affine_word_view(prefix++parameters) valuation current -> temp_agree pointers initial current ->
  current!helper=Some(Vint(Int.repr upper)) ->
  exec_stmt fe ge locals current before(constant_body_source iterator(Int.repr upper) body) E0 exit last Out_normal ->
  header_observations_match(map word_observer_snapshot observers) before ->
  header_observations_match(map word_observer_snapshot observers) last.
Proof.
  intros CHECK CURRENT_WORDS CURRENT_POINTERS CURRENT_HELPER CURRENT_SOURCE MATCH.
  unfold header_observations_match in *; apply Forall_forall.
  intros snapshot MEMBER; apply in_map_iff in MEMBER as [observer [<- OBSERVER]].
  assert (KEEP : location_load(word_observer_location observer) last=location_load(word_observer_location observer) before).
  { eapply constant_affine_prefix_writes_preserve with(certificate:=certificate); try eassumption.
    exact(constant_body_joint_scan_writes_apart observer OBSERVER CHECK). }
  cbn [word_observer_snapshot fst snd]; rewrite KEEP.
  apply Forall_forall with(x:=word_observer_snapshot observer) in MATCH;
    [exact MATCH|apply in_map; exact OBSERVER].
Qed.

Theorem constant_body_joint_scan_inner_preserved column stable j :
  incl(prefix++parameters)(column::stable) -> incl pointers stable -> In helper stable ->
  initial!helper=Some(Vint(Int.repr upper)) ->
  affine_word_view(prefix++parameters) valuation(PTree.set column(Vint(Int.repr j)) initial) ->
  affine_scan_result nest valuation 0(affine_joint_observation_result locations observers operations)=true ->
  expression_body_preserved fe column(constant_body_source iterator(Int.repr upper) body) stable
    (fun _=>map word_observer_snapshot observers) j(Entry ge locals initial guard_memory).
Proof.
  intros WORD_SCOPE POINTER_STABLE HELPER_STABLE INITIAL_HELPER ENTRY_WORDS CHECK current before exit last COLUMN FRAME MATCH RUN.
  assert (CURRENT_WORDS : affine_word_view(prefix++parameters) valuation current).
  { eapply affine_word_view_frame; [exact ENTRY_WORDS|].
    intros identifier MEMBER; specialize(WORD_SCOPE identifier MEMBER); destruct WORD_SCOPE as [SAME|STABLE].
    - subst identifier; rewrite PTree.gss; exact COLUMN.
    - destruct(Pos.eq_dec identifier column) as [->|OTHER]; [rewrite PTree.gss; exact COLUMN|].
      rewrite PTree.gso by exact OTHER; exact(FRAME identifier STABLE). }
  eapply constant_body_joint_scan_preserves_all_sources;
    [exact CHECK|exact CURRENT_WORDS| | |exact RUN|exact MATCH].
  - eapply temp_agree_weaken; eassumption.
  - rewrite FRAME by exact HELPER_STABLE; exact INITIAL_HELPER.
Qed.

Theorem constant_body_joint_scan_inner_advance column cache bound stable source_written ready j :
  typeof bound=type_int32s -> ~In column stable ->
  normal_statement(constant_body_source iterator(Int.repr upper) body)=true ->
  quiet_statement(constant_body_source iterator(Int.repr upper) body)=true ->
  writes_only source_written(constant_body_source iterator(Int.repr upper) body) ->
  ~In column source_written -> (forall id,In id stable -> ~In id source_written) ->
  (forall entry k current before,ready entry -> 0<=k<=Int.signed(temp_word cache(entry_temps entry)) ->
    current!column=Some(Vint(Int.repr k)) -> temp_agree stable(entry_temps entry) current ->
    header_observations_match(map word_observer_snapshot observers) before ->
    eval_expr(entry_ge entry)(entry_env entry) current before bound(Vint(temp_word cache(entry_temps entry)))) ->
  incl(prefix++parameters)(column::stable) -> incl pointers stable -> In helper stable ->
  initial!helper=Some(Vint(Int.repr upper)) ->
  affine_word_view(prefix++parameters) valuation(PTree.set column(Vint(Int.repr j)) initial) ->
  affine_scan_result nest valuation 0(affine_joint_observation_result locations observers operations)=true ->
  expression_body_prefix fe column cache bound(constant_body_source iterator(Int.repr upper) body) stable ready
    (fun _=>map word_observer_snapshot observers) j(Entry ge locals initial guard_memory) ->
  j<Int.signed(temp_word cache initial) ->
  expression_body_prefix fe column cache bound(constant_body_source iterator(Int.repr upper) body) stable ready
    (fun _=>map word_observer_snapshot observers)(j+1)(Entry ge locals initial guard_memory).
Proof.
  intros TYPE COLUMN_PRIVATE NORMAL QUIET SOURCE_WRITES COLUMN_UNWRITTEN STABLE_UNWRITTEN HEADER
    WORD_SCOPE POINTER_STABLE HELPER_STABLE INITIAL_HELPER ENTRY_WORDS CHECK PREFIX ACTIVE.
  eapply expression_body_prefix_advance with(written:=source_written); try eassumption.
  - intros other_ge other_locals current before exit last RUN; eapply structured_memory_accesses_back; eassumption.
  - eapply constant_body_joint_scan_inner_preserved; eassumption.
Qed.
End BODY.

Print Assumptions constant_affine_prefix_writes_preserve.
Print Assumptions constant_body_scan_point_capable.
Print Assumptions constant_body_scan_write_binding.
Print Assumptions constant_body_joint_point_test.
Print Assumptions constant_body_joint_leaf_execution.
Print Assumptions constant_body_joint_scan_execution.
Print Assumptions constant_body_joint_scan_writes_apart.
Print Assumptions constant_body_joint_scan_preserves_observation.
Print Assumptions constant_body_joint_scan_preserves_snapshots.
Print Assumptions constant_body_joint_scan_preserves_all_sources.
Print Assumptions constant_body_joint_scan_inner_preserved.
Print Assumptions constant_body_joint_scan_inner_advance.
