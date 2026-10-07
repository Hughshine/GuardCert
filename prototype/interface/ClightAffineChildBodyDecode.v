From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightTempFrame ClightNoWrap ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops GuardMemoryAffineSourceExpressions
  GuardMemoryWindowCells.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestWords AffineNestValuation
  AffineNestMathDomain AffineNestSourceDecode AffineNestLeafDecode AffineNestLeafModel AffineNestLoopEncoding.
Import ListNotations.
Set Implicit Arguments.

(** The existing recursive source decoder already supports a coordinate
    prefix. This checked-leaf adapter exposes that capability for one body
    without asking for completion of its enclosing cached loop. *)
Theorem affine_checked_prefix_source_decode nest coordinates prefix parameters bounds lower upper pointers operations
  (certificate : affine_leaf_certificate(affine_nest_leaf nest) bounds lower upper (coordinates++parameters) [] pointers operations)
  fe ge locals initial valuation start code temps memory after final tail :
  coordinates=prefix++affine_nest_iterators nest ->
  affine_nest_shapes nest -> NoDup(affine_nest_controls nest) ->
  affine_nest_bound_dependencies prefix parameters nest ->
  (forall identifier, In identifier((prefix++parameters)++pointers) -> ~In identifier(affine_nest_mutated nest)) ->
  affine_math_domain bounds (coordinates++parameters) nest valuation start ->
  affine_word_view(prefix++parameters) valuation temps -> temp_agree pointers initial temps ->
  affine_nest_entry nest valuation start temps ->
  affine_lower_nest nest prefix parameters (L.Constant start)
    (affine_checked_leaf_code coordinates parameters [] operations)=Some code ->
  exec_stmt fe ge locals temps memory (affine_nest_source nest) E0 after final Out_normal ->
  L.loop_semantics code (map valuation(rev prefix++parameters)++tail)
    (RuntimeState(window_multi_pointer_locations initial lower upper) memory)
    (RuntimeState(window_multi_pointer_locations initial lower upper) final).
Proof.
  intros COORDINATES SHAPES FRESH DEPENDENCIES PROTECTED DOMAIN WORDS POINTERS ENTRY LOWER SOURCE.
  eapply affine_nest_source_decode with(pointers:=pointers)(original:=initial)(bounds:=bounds)
    (layout:=coordinates++parameters)(coordinates:=coordinates)(source_leaf:=affine_nest_leaf nest)
    (target_leaf:=affine_checked_leaf_code coordinates parameters [] operations)(prefix:=prefix)
    (parameters:=parameters)(valuation:=valuation)(lower:=start)(lower_code:=L.Constant start);
    try eassumption; try reflexivity.
  - exact(affine_leaf_normal certificate).
  - exact(affine_leaf_quiet certificate).
  - exact(affine_leaf_writes certificate).
  - intros leaf_prefix leaf_valuation leaf_temps before leaf_after last SAME LEAF_WORDS LEAF_POINTERS RANGES LEAF.
    subst leaf_prefix.
    assert (ALL_WORDS : affine_word_view(coordinates++(parameters++[])) leaf_valuation leaf_temps)
      by (rewrite app_nil_r; exact LEAF_WORDS).
    pose proof(@affine_checked_leaf_decode _ bounds lower upper coordinates parameters [] pointers operations certificate
      fe ge locals leaf_valuation initial leaf_temps before leaf_after last tail ALL_WORDS LEAF_POINTERS RANGES LEAF) as DECODE.
    rewrite app_nil_r in DECODE; exact DECODE.
Qed.

(** Body setup is decoded using the same checked source shape and affine
    expression/word correspondence as the original whole-nest proof. *)
Theorem affine_child_body_source_decode iterator bound expression body child parameters bounds lower upper pointers operations
  (certificate : affine_leaf_certificate(affine_nest_leaf child) bounds lower upper
    ((iterator::affine_nest_iterators child)++parameters) [] pointers operations)
  fe ge locals initial valuation code temps memory after final tail :
  affine_nest_shapes(AffineSourceAxis iterator bound expression body child) ->
  NoDup(affine_nest_controls(AffineSourceAxis iterator bound expression body child)) ->
  affine_nest_bound_dependencies [iterator] parameters child ->
  (forall identifier, In identifier(parameters++pointers) ->
    ~In identifier(affine_nest_mutated(AffineSourceAxis iterator bound expression body child))) ->
  affine_math_domain bounds ((iterator::affine_nest_iterators child)++parameters) child valuation 0 ->
  affine_word_view parameters valuation temps -> temps!iterator=Some(Vint(Int.repr(valuation iterator))) ->
  temp_agree pointers initial temps ->
  affine_lower_nest child [iterator] parameters (L.Constant 0)
    (affine_checked_leaf_code(iterator::affine_nest_iterators child) parameters [] operations)=Some code ->
  exec_stmt fe ge locals temps memory body E0 after final Out_normal ->
  L.loop_semantics code (map valuation(iterator::parameters)++tail)
    (RuntimeState(window_multi_pointer_locations initial lower upper) memory)
    (RuntimeState(window_multi_pointer_locations initial lower upper) final).
Proof.
  intros [SHAPE SHAPES] FRESH DEPENDENCIES PROTECTED DOMAIN WORDS ROW POINTERS LOWER SOURCE.
  assert (ROOT_PRIVATE : ~In iterator(affine_nest_controls child)).
  { cbn [affine_nest_controls] in FRESH; apply NoDup_cons_iff in FRESH as [ROOT REST].
    intro MEMBER; apply ROOT; right; exact MEMBER. }
  assert (CHILD_FRESH : NoDup(affine_nest_controls child)).
  { cbn [affine_nest_controls] in FRESH; apply NoDup_cons_iff in FRESH as [_ REST].
    apply NoDup_cons_iff in REST; tauto. }
  assert (ALL_PROTECTED : forall identifier, In identifier((iterator::parameters)++pointers) ->
    ~In identifier(affine_nest_controls child)).
  { intros identifier MEMBER BAD; cbn in MEMBER; destruct MEMBER as [SAME|MEMBER].
    - subst identifier; exact(ROOT_PRIVATE BAD).
    - apply(PROTECTED identifier MEMBER); cbn [affine_nest_mutated]; right; exact BAD. }
  assert (ENTRY_WORDS : affine_word_view(iterator::parameters) valuation temps).
  { intros identifier MEMBER; cbn in MEMBER; destruct MEMBER as [SAME|MEMBER]; [subst; exact ROW|apply WORDS; exact MEMBER]. }
  destruct child as [leaf|child_iterator child_bound child_expression child_body grandchild].
  - cbn [affine_nest_child_shape] in SHAPE; subst body.
    cbn [affine_lower_nest] in LOWER; inversion LOWER; subst code.
    assert (ALL_WORDS : affine_word_view([iterator]++(parameters++[])) valuation temps)
      by (rewrite app_nil_r; exact ENTRY_WORDS).
    pose proof(@affine_checked_leaf_decode _ bounds lower upper [iterator] parameters [] pointers operations certificate
      fe ge locals valuation initial temps memory after final tail ALL_WORDS POINTERS DOMAIN SOURCE) as DECODE.
    rewrite app_nil_r in DECODE; exact DECODE.
  - destruct(@affine_exit_fresh_child child_iterator child_bound child_expression child_body grandchild CHILD_FRESH)
      as [GRANDCHILD_FRESH [BOUND_PRIVATE DISTINCT]].
    destruct(@affine_child_setup_decode fe ge locals child_iterator child_bound child_expression child_body body
      temps memory after final DISTINCT SHAPE SOURCE) as [word [EVAL CHILD_SOURCE]].
    destruct DEPENDENCIES as [READS GRANDCHILD_DEPENDENCIES].
    pose proof(@affine_bound_word_from_view child_expression (iterator::parameters) valuation ge locals temps memory word
      READS ENTRY_WORDS EVAL) as VALUE; subst word.
    eapply affine_checked_prefix_source_decode with(prefix:=[iterator])(start:=0)
      (temps:=PTree.set child_iterator (Vint Int.zero)
        (PTree.set child_bound (Vint(Int.repr(memory_source_affine_math valuation child_expression))) temps));
      try eassumption; try reflexivity.
    + split; assumption.
    + intros identifier MEMBER BAD; apply(ALL_PROTECTED identifier MEMBER).
      cbn [affine_nest_mutated affine_nest_controls List.In] in *; intuition.
    + eapply affine_word_view_frame; [exact ENTRY_WORDS|].
      eapply temp_agree_trans; apply temp_agree_set; intro MEMBER;
        apply(ALL_PROTECTED _ (in_or_app _ _ _ (or_introl MEMBER))); cbn; auto.
    + eapply temp_agree_trans; [exact POINTERS|].
      eapply temp_agree_trans; apply temp_agree_set; intro MEMBER;
        apply(ALL_PROTECTED _ (in_or_app _ _ _ (or_intror MEMBER))); cbn; auto.
    + split; [apply PTree.gss|rewrite PTree.gso by congruence; apply PTree.gss].
Qed.

Print Assumptions affine_checked_prefix_source_decode.
Print Assumptions affine_child_body_source_decode.
