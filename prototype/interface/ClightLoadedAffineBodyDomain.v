From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightTempFrame ClightRedundantSet.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops GuardMemoryWindowCells
  GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation GuardMemoryFootprintCapabilities
  GuardMemoryNaryCompute GuardMemoryRectangularFootprint.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestValuation AffineNestMathDomain
  AffineNestFirstDomain AffineNestProbe AffineNestDomainGuard AffineNestGuardDomain AffineNestGuardPackage
  AffineNestGuardParameterCheck AffineNestPackageGuard AffineNestLeafModel AffineNestLeafDecode
  AffineNestLoopEncoding AffineNestLeafLoop AffineNestScanPoints AffineNestScanModel AffineNestSourceDecode.
From GuardInterface Require Import ClightAffineFirstBodyReceipt ClightLoadedAffineFirstPath
  ClightLoadedAffineNumericGuard ClightLoadedAffineBodyPrefix ClightLoadedBodyPrefix
  ClightAffineChildBodyDecode ClightAffineBodyCapabilities ClightStorePermissions.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Numeric acceptance exposes only parameters actually used by the checked
    source. Their word values come from the original first-body receipt, not
    from completion of a hypothetical cached root loop. *)
Theorem affine_receipted_package_word_view source parameters live proposal
  (package : affine_guard_package source parameters live proposal) fe ge locals temps memory :
  affine_first_body_receipt (affine_proposed_iterator proposal) (affine_proposed_bound proposal)
    (affine_proposed_body proposal) fe (Entry ge locals temps memory) ->
  affine_package_guard_flag parameters proposal (Entry ge locals temps memory)=true ->
  affine_word_view parameters (affine_word_valuation temps) temps.
Proof.
  intros RECEIPT ACCEPT.
  unfold affine_package_guard_flag,affine_domain_guard_flag in ACCEPT.
  apply andb_true_iff in ACCEPT as [ACTIVE NUMERIC].
  cbn [entry_temps] in ACTIVE; apply affine_first_path_flag_exact in ACTIVE.
  pose proof (described_affine_shapes (affine_package_description package)) as SHAPES;
    rewrite (affine_package_nest package) in SHAPES.
  pose proof (@affine_nest_fresh_controls _ (described_affine_fresh (affine_package_description package))) as FRESH;
    rewrite (affine_package_nest package) in FRESH.
  apply affine_register_domains_word_view with(ge:=ge)(locals:=locals)(memory:=memory).
  eapply affine_first_body_parameter_domains;
    [exact SHAPES|exact FRESH|exact (affine_leaf_normal (affine_package_leaf package))|
     exact (affine_leaf_quiet (affine_package_leaf package))|exact (affine_leaf_writes (affine_package_leaf package))|
     exact RECEIPT|exact (affine_package_leaf package)|exact (affine_package_used package)|exact ACTIVE].
Qed.

Definition affine_loaded_body_ready parameters proposal entry :=
  affine_loaded_numeric_premise parameters proposal entry /\
  (entry_temps entry)!(affine_proposed_iterator proposal)=Some(Vint Int.zero) /\
  affine_word_view parameters (affine_word_valuation (entry_temps entry)) (entry_temps entry).

Definition affine_loaded_body_model parameters proposal :=
  affine_lower_nest (affine_proposed_child proposal) [affine_proposed_iterator proposal] parameters (L.Constant 0)
    (affine_checked_leaf_code (affine_proposed_iterator proposal::affine_nest_iterators(affine_proposed_child proposal))
      parameters [] (affine_proposed_operations proposal)).

Theorem affine_loaded_body_ready_from_source source parameters live proposal pointer
  (package : affine_guard_package source parameters live proposal) fe ge locals temps memory after final :
  affine_loaded_numeric_snapshot pointer proposal (Entry ge locals temps memory) ->
  affine_loaded_numeric_premise parameters proposal (Entry ge locals temps memory) ->
  temps!(affine_proposed_iterator proposal)=Some(Vint Int.zero) ->
  exec_stmt fe ge locals temps memory (affine_loaded_numeric_source pointer proposal) E0 after final Out_normal ->
  affine_loaded_body_ready parameters proposal (Entry ge locals temps memory).
Proof.
  intros [block [offset [upper [POINTER [READ CACHE]]]]] NUMERIC ROW SOURCE.
  split; [exact NUMERIC|split; [exact ROW|]].
  destruct (affine_loaded_numeric_body_properties package) as [NORMAL QUIET].
  eapply affine_receipted_package_word_view; [exact package| |exact (proj1 NUMERIC)].
  exact (@loaded_affine_first_body_receipt fe ge locals temps memory
    (affine_proposed_iterator proposal) pointer (affine_proposed_bound proposal) (affine_proposed_body proposal)
    after final block offset upper NORMAL QUIET POINTER READ CACHE SOURCE).
Qed.

Section BODY.
Variables source : statement.
Variables parameters live : list ident.
Variable proposal : affine_guard_proposal.
Variable package : affine_guard_package source parameters live proposal.
Variable pointer : ident.
Hypothesis NAMES : affine_loaded_body_names_check proposal pointer=true.

Theorem affine_loaded_ready_initial_prefix fe ge locals temps memory after final :
  affine_loaded_numeric_snapshot pointer proposal (Entry ge locals temps memory) ->
  affine_loaded_numeric_premise parameters proposal (Entry ge locals temps memory) ->
  temps!(affine_proposed_iterator proposal)=Some(Vint Int.zero) ->
  0<=Int.signed(temp_word (affine_proposed_bound proposal) temps) ->
  exec_stmt fe ge locals temps memory (affine_loaded_numeric_source pointer proposal) E0 after final Out_normal ->
  loaded_body_prefix fe (affine_proposed_iterator proposal)(affine_proposed_bound proposal) pointer
    (affine_proposed_body proposal)(affine_loaded_body_stable parameters proposal pointer)
    (affine_loaded_body_ready parameters proposal) 0 (Entry ge locals temps memory).
Proof.
  intros SNAPSHOT NUMERIC ROW NONNEGATIVE SOURCE.
  pose proof (@affine_loaded_body_ready_from_source source parameters live proposal pointer package
    fe ge locals temps memory after final SNAPSHOT NUMERIC ROW SOURCE) as READY.
  destruct SNAPSHOT as [block [offset [upper [POINTER [READ CACHE]]]]].
  cbn [entry_temps entry_memory] in POINTER,READ,CACHE.
  eapply loaded_body_prefix_initial with(block:=block)(offset:=offset)(after:=after)(final:=final);
    try eassumption; [exists upper; exact CACHE|].
  cbn [entry_temps]; unfold temp_word; rewrite CACHE; exact READ.
Qed.

Theorem affine_loaded_ready_body_decode fe entry i code current memory after final tail :
  affine_loaded_body_ready parameters proposal entry ->
  0<=i<Int.signed(temp_word (affine_proposed_bound proposal)(entry_temps entry)) ->
  current!(affine_proposed_iterator proposal)=Some(Vint(Int.repr i)) ->
  temp_agree (affine_loaded_body_stable parameters proposal pointer) (entry_temps entry) current ->
  affine_lower_nest (affine_proposed_child proposal) [affine_proposed_iterator proposal] parameters (L.Constant 0)
    (affine_checked_leaf_code (affine_proposed_iterator proposal::affine_nest_iterators(affine_proposed_child proposal))
      parameters [] (affine_proposed_operations proposal))=Some code ->
  exec_stmt fe (entry_ge entry)(entry_env entry) current memory (affine_proposed_body proposal)
    E0 after final Out_normal ->
  L.loop_semantics code
    (map (memory_source_set_valuation (affine_word_valuation(entry_temps entry)) (affine_proposed_iterator proposal) i)
      (affine_proposed_iterator proposal::parameters)++tail)
    (RuntimeState(window_multi_pointer_locations(entry_temps entry)
      (affine_proposed_window_lower proposal)(affine_proposed_window_upper proposal)) memory)
    (RuntimeState(window_multi_pointer_locations(entry_temps entry)
      (affine_proposed_window_lower proposal)(affine_proposed_window_upper proposal)) final).
Proof.
  intros [[ACCEPT DOMAIN] [INITIAL_ROW WORDS]] RANGE ROW FRAME LOWER BODY.
  pose proof (described_affine_shapes (affine_package_description package)) as SHAPES;
    rewrite (affine_package_nest package) in SHAPES.
  pose proof (@affine_nest_fresh_controls _ (described_affine_fresh (affine_package_description package))) as FRESH;
    rewrite (affine_package_nest package) in FRESH.
  pose proof (described_affine_dependencies (affine_package_description package)) as DEPENDENCIES;
    rewrite (affine_package_nest package) in DEPENDENCIES.
  destruct (@affine_loaded_body_controls source parameters live proposal package pointer NAMES) as [ROOT PROTECTED].
  assert (INITIAL_ZERO : affine_word_valuation(entry_temps entry)(affine_proposed_iterator proposal)=0).
  { unfold affine_word_valuation,temp_word; rewrite INITIAL_ROW; reflexivity. }
  cbn [affine_math_domain affine_proposal_nest memory_source_affine_math] in DOMAIN.
  rewrite INITIAL_ZERO in DOMAIN.
  assert (CHILD_DOMAIN : affine_math_domain (affine_proposed_leaf_bounds proposal)(affine_proposal_layout proposal parameters)
    (affine_proposed_child proposal)
    (memory_source_set_valuation(affine_word_valuation(entry_temps entry))(affine_proposed_iterator proposal) i) 0).
  { apply (proj2(proj2 DOMAIN)); exact RANGE. }
  assert (PARAMETERS : affine_word_view parameters
    (memory_source_set_valuation(affine_word_valuation(entry_temps entry))(affine_proposed_iterator proposal) i) current).
  { intros identifier MEMBER; unfold memory_source_set_valuation.
    destruct (peq identifier (affine_proposed_iterator proposal)) as [SAME|OTHER].
    - subst identifier; exfalso; apply (PROTECTED _ (or_intror(or_intror(in_or_app _ _ _ (or_introl MEMBER))))).
      cbn [affine_nest_mutated affine_proposal_nest]; left; reflexivity.
    - rewrite FRAME; [apply WORDS; exact MEMBER|right; right; apply in_or_app; left; exact MEMBER]. }
  eapply (@affine_child_body_source_decode (affine_proposed_iterator proposal)(affine_proposed_bound proposal)
    (MemorySourceTemp(affine_proposed_bound proposal))(affine_proposed_body proposal)(affine_proposed_child proposal)
    parameters (affine_proposed_leaf_bounds proposal)(affine_proposed_window_lower proposal)(affine_proposed_window_upper proposal)
    (affine_proposed_pointers proposal)(affine_proposed_operations proposal)(affine_package_leaf package)
    fe (entry_ge entry)(entry_env entry)(entry_temps entry)
    (memory_source_set_valuation(affine_word_valuation(entry_temps entry))(affine_proposed_iterator proposal) i)
    code current memory after final tail); try eassumption.
  - exact (proj2 DEPENDENCIES).
  - intros identifier MEMBER; apply PROTECTED; right; right; exact MEMBER.
  - unfold memory_source_set_valuation; destruct (peq (affine_proposed_iterator proposal)(affine_proposed_iterator proposal));
      [exact ROW|contradiction].
  - intros identifier MEMBER; apply FRAME; right; right; apply in_or_app; right; exact MEMBER.
Qed.

(** At an active prefix, the real remaining source supplies one complete
    body. Decode that body and transport its physical cell capabilities back
    to the entry where a read-only/private-state guard actually runs. *)
Theorem affine_loaded_prefix_point_capabilities fe i entry code :
  loaded_body_prefix fe (affine_proposed_iterator proposal)(affine_proposed_bound proposal) pointer
    (affine_proposed_body proposal)(affine_loaded_body_stable parameters proposal pointer)
    (affine_loaded_body_ready parameters proposal) i entry ->
  i<Int.signed(temp_word (affine_proposed_bound proposal)(entry_temps entry)) ->
  affine_lower_nest (affine_proposed_child proposal) [affine_proposed_iterator proposal] parameters (L.Constant 0)
    (affine_checked_leaf_code (affine_proposed_iterator proposal::affine_nest_iterators(affine_proposed_child proposal))
      parameters [] (affine_proposed_operations proposal))=Some code ->
  forall point, affine_scan_point (affine_proposed_child proposal)
    (memory_source_set_valuation(affine_word_valuation(entry_temps entry))(affine_proposed_iterator proposal) i) 0 point ->
  Forall (memory_cell_capable (window_multi_pointer_locations(entry_temps entry)
    (affine_proposed_window_lower proposal)(affine_proposed_window_upper proposal))(entry_memory entry))
    (memory_point_footprint (map memory_nary_compute_instruction (affine_proposed_operations proposal))
      (map point(affine_proposal_layout proposal parameters))).
Proof.
  intros PREFIX ACTIVE LOWER point POINT.
  pose proof PREFIX as [READY [CACHE [RANGE REST]]].
  destruct (affine_loaded_numeric_body_properties package) as [NORMAL QUIET].
  destruct (@loaded_body_prefix_receipt fe (affine_proposed_iterator proposal)(affine_proposed_bound proposal) pointer
    (affine_proposed_body proposal)(affine_loaded_body_stable parameters proposal pointer)
    (affine_loaded_body_ready parameters proposal) (or_intror(or_introl eq_refl)) NORMAL QUIET i entry PREFIX ACTIVE)
    as [block [offset [current [memory [after [final [POINTER [ROW [FRAME [READ [BACK BODY]]]]]]]]]]].
  pose proof (@affine_loaded_ready_body_decode fe entry i code current memory after final []
    READY ltac:(lia) ROW FRAME LOWER BODY) as MODEL.
  unfold affine_checked_leaf_code in LOWER; rewrite app_nil_r in LOWER.
  pose proof (affine_leaf_unique(affine_package_leaf package)) as UNIQUE; rewrite app_nil_r in UNIQUE.
  eapply affine_prefix_capabilities_at_guard_entry with(prefix:=[affine_proposed_iterator proposal])
    (lower:=0)(lower_code:=L.Constant 0)(code:=code)(tail:=[])(memory:=memory)(final:=final);
    try eassumption; try reflexivity.
  exact (window_multi_pointer_locations_int32 _ _ _).
Qed.
End BODY.

Print Assumptions affine_receipted_package_word_view.
Print Assumptions affine_loaded_body_ready_from_source.
Print Assumptions affine_loaded_ready_initial_prefix.
Print Assumptions affine_loaded_ready_body_decode.
Print Assumptions affine_loaded_prefix_point_capabilities.
