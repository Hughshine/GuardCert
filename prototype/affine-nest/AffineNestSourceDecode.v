From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCountedLoop ClightTempFrame ClightLoopSyntax ClightRegionProgress.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops GuardMemoryAffineSourceExpressions
  GuardMemoryAffineSourceValuation GuardMemoryIntervalBox.
From GuardAffineNest Require Import AffineNestSyntax AffineNestWords AffineNestExit AffineNestSourceShape
  AffineNestLoopEncoding AffineNestExpressionTail AffineNestMemoryProjection AffineNestLoopProjection
  AffineNestValuation AffineNestMathDomain.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition affine_nest_mutated nest := match nest with
  | AffineSourceLeaf _ => []
  | AffineSourceAxis iterator _ _ _ child => iterator::affine_nest_controls child end.
Definition affine_nest_entry nest valuation lower temps := match nest with
  | AffineSourceLeaf _ => True
  | AffineSourceAxis iterator bound expression _ _ =>
      temps!iterator=Some(Vint(Int.repr lower)) /\
      temps!bound=Some(Vint(Int.repr(memory_source_affine_math valuation expression))) end.

Section DECODE.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable pointers : list ident.
Variable original : temp_env.
Variable locations : cell_locations.
Variable source_leaf : statement.
Variable target_leaf : L.stmt.
Variable bounds : list (Z*Z).
Variable layout : list ident.
Variable coordinates : list ident.
Variable parameters : list ident.
Variable tail : list Z.
Hypothesis LEAF_NORMAL : normal_statement source_leaf=true.
Hypothesis LEAF_QUIET : quiet_statement source_leaf=true.
Hypothesis LEAF_WRITES : writes_only [] source_leaf.
Hypothesis LEAF_DECODE : forall prefix valuation temps memory after final,
  coordinates=prefix ->
  affine_word_view (prefix++parameters) valuation temps ->
  temp_agree pointers original temps -> interval_ranges bounds(map valuation layout) ->
  exec_stmt fe ge locals temps memory source_leaf E0 after final Out_normal ->
  L.loop_semantics target_leaf (map valuation(rev prefix++parameters)++tail)
    (RuntimeState locations memory) (RuntimeState locations final).

(** Recursive source-to-Loop composition. Its leaf premise is discharged by
    the independently checked real memory leaf adapter; its integer domain
    still has to be supplied by a generated, proved runtime guard. *)
Theorem affine_nest_source_decode nest : forall prefix valuation lower lower_code code temps memory after final,
  coordinates=prefix++affine_nest_iterators nest ->
  affine_nest_leaf nest=source_leaf -> affine_nest_shapes nest -> NoDup(affine_nest_controls nest) ->
  affine_nest_bound_dependencies prefix parameters nest ->
  (forall identifier, In identifier ((prefix++parameters)++pointers) ->
    ~In identifier(affine_nest_mutated nest)) ->
  affine_math_domain bounds layout nest valuation lower ->
  affine_word_view (prefix++parameters) valuation temps -> temp_agree pointers original temps ->
  affine_nest_entry nest valuation lower temps ->
  affine_lower_nest nest prefix parameters lower_code target_leaf=Some code ->
  L.eval_expr (map valuation(rev prefix++parameters)++tail) lower_code=lower ->
  exec_stmt fe ge locals temps memory (affine_nest_source nest) E0 after final Out_normal ->
  L.loop_semantics code (map valuation(rev prefix++parameters)++tail)
    (RuntimeState locations memory) (RuntimeState locations final).
Proof.
  induction nest as [source|iterator bound expression body child IH];
    intros prefix valuation lower lower_code code temps memory after final COORDINATES LEAF SHAPES FRESH DEPENDENCIES
      PROTECTED DOMAIN WORDS POINTERS ENTRY LOWER VALUE SOURCE.
  - cbn [affine_nest_leaf] in LEAF; subst source.
    cbn [affine_lower_nest] in LOWER; inversion LOWER; subst code.
    cbn [affine_nest_iterators] in COORDINATES; rewrite app_nil_r in COORDINATES.
    eapply LEAF_DECODE; eassumption.
  - destruct (@affine_lower_nest_axis iterator bound expression body child prefix parameters
      lower_code target_leaf code LOWER) as [upper_code [child_code [UPPER [CHILD CODE]]]]; subst code.
    cbn [affine_nest_leaf] in LEAF.
    destruct DOMAIN as [SIGNED_LOWER [SIGNED_UPPER CHILD_DOMAIN]].
    destruct ENTRY as [ITERATOR BOUND].
    destruct DEPENDENCIES as [READS CHILD_DEPENDENCIES].
    destruct (@affine_exit_fresh_child iterator bound expression body child FRESH)
      as [CHILD_FRESH [BOUND_PRIVATE DISTINCT]].
    assert (ITERATOR_PRIVATE:~In iterator(affine_nest_controls child)).
    { inversion FRESH; subst; cbn in H1; intuition. }
    assert (LEAF_NORMAL_CHILD:normal_statement(affine_nest_leaf child)=true) by (rewrite LEAF; exact LEAF_NORMAL).
    assert (LEAF_QUIET_CHILD:quiet_statement(affine_nest_leaf child)=true) by (rewrite LEAF; exact LEAF_QUIET).
    assert (LEAF_WRITES_CHILD:writes_only [] (affine_nest_leaf child)) by (rewrite LEAF; exact LEAF_WRITES).
    eapply affine_frontend_loop_projection with
      (fe:=fe) (ge:=ge) (locals:=locals) (body:=body)
      (protected:=((prefix++parameters)++pointers)) (written:=affine_nest_controls child)
      (original:=temps) (start:=lower) (finish:=memory_source_affine_math valuation expression).
    + exact DISTINCT.
    + eapply affine_nest_body_normal; eassumption.
    + eapply affine_nest_body_writes; eassumption.
    + exact ITERATOR_PRIVATE.
    + exact BOUND_PRIVATE.
    + intro MEMBER; apply(PROTECTED iterator MEMBER); exact(or_introl eq_refl).
    + intros identifier MEMBER BAD; apply(PROTECTED identifier MEMBER); cbn [affine_nest_mutated]; right; exact BAD.
    + exact SIGNED_LOWER.
    + exact SIGNED_UPPER.
    + exact VALUE.
    + eapply affine_loop_expression_tail_value; exact UPPER.
    + exact ITERATOR.
    + exact BOUND.
    + apply temp_agree_refl.
    + intros value first last RANGE [point_temps [point_after [FRAME [POINT_ITERATOR BODY]]]].
      set (next_valuation:=memory_source_set_valuation valuation iterator value).
      assert (POINT_WORDS:affine_word_view ((prefix++[iterator])++parameters) next_valuation point_temps).
      { intros identifier MEMBER; unfold next_valuation,memory_source_set_valuation.
        destruct(peq identifier iterator) as [->|OTHER]; [exact POINT_ITERATOR|].
        rewrite (FRAME identifier).
        - apply WORDS; apply in_app_or in MEMBER; destruct MEMBER as [MEMBER|MEMBER]; [|apply in_or_app; auto].
          apply in_app_or in MEMBER; destruct MEMBER as [MEMBER|MEMBER]; [apply in_or_app; auto|].
          cbn in MEMBER; intuition congruence.
        - apply in_or_app; left; apply in_app_or in MEMBER; destruct MEMBER as [MEMBER|MEMBER]; [|apply in_or_app; auto].
          apply in_app_or in MEMBER; destruct MEMBER as [MEMBER|MEMBER]; [apply in_or_app; auto|].
          cbn in MEMBER; intuition congruence. }
      assert (POINT_POINTERS:temp_agree pointers original point_temps).
      { intros identifier MEMBER; rewrite (FRAME identifier (in_or_app _ _ _ (or_intror MEMBER))); apply POINTERS; exact MEMBER. }
      assert (OLD_PROTECTED:forall identifier, In identifier ((prefix++parameters)++pointers) ->
        ~In identifier(affine_nest_controls child)).
      { intros identifier MEMBER BAD; apply(PROTECTED identifier MEMBER); exact(or_intror BAD). }
      assert (NEXT_CONTROLS:forall identifier, In identifier (((prefix++[iterator])++parameters)++pointers) ->
        ~In identifier(affine_nest_controls child)).
      { intros identifier MEMBER BAD; repeat rewrite in_app_iff in MEMBER; cbn in MEMBER.
        destruct MEMBER as [[[MEMBER|[SAME|FALSE]]|MEMBER]|MEMBER].
        - apply(OLD_PROTECTED identifier); [apply in_or_app; left; apply in_or_app; auto|exact BAD].
        - subst identifier; exact(ITERATOR_PRIVATE BAD).
        - contradiction.
        - apply(OLD_PROTECTED identifier); [apply in_or_app; left; apply in_or_app; auto|exact BAD].
        - apply(OLD_PROTECTED identifier); [apply in_or_app; auto|exact BAD]. }
      assert (NEXT_PROTECTED:forall identifier, In identifier (((prefix++[iterator])++parameters)++pointers) ->
        ~In identifier(affine_nest_mutated child)).
      { intros identifier MEMBER BAD; apply(NEXT_CONTROLS identifier MEMBER).
        destruct child; cbn [affine_nest_mutated affine_nest_controls List.In] in *; [contradiction|intuition]. }
      assert (CHILD_COORDINATES:coordinates=(prefix++[iterator])++affine_nest_iterators child).
      { rewrite COORDINATES; cbn [affine_nest_iterators]; rewrite <-app_assoc; reflexivity. }
      assert (ENVIRONMENT:map next_valuation(rev(prefix++[iterator])++parameters)++tail=
        value::(map valuation(rev prefix++parameters)++tail)).
      { apply affine_valuation_loop_environment; intro MEMBER; apply(PROTECTED iterator);
          [apply in_or_app; auto|exact(or_introl eq_refl)]. }
      rewrite <-ENVIRONMENT.
      destruct SHAPES as [SHAPE CHILD_SHAPES].
      destruct child as [leaf|child_iterator child_bound child_expression child_body grandchild].
      * cbn [affine_nest_child_shape] in SHAPE; subst body.
        eapply IH with (lower:=0) (lower_code:=L.Constant 0); try eassumption; try reflexivity.
        -- apply CHILD_DOMAIN; exact RANGE.
      * destruct (@affine_exit_fresh_child child_iterator child_bound child_expression child_body grandchild CHILD_FRESH)
          as [GRANDCHILD_FRESH [CHILD_BOUND_PRIVATE CHILD_DISTINCT]].
        destruct (@affine_child_setup_decode fe ge locals child_iterator child_bound child_expression child_body body
          point_temps first point_after last CHILD_DISTINCT SHAPE BODY) as [word [EVAL CHILD_SOURCE]].
        destruct CHILD_DEPENDENCIES as [CHILD_READS GRANDCHILD_DEPENDENCIES].
        pose proof (@affine_bound_word_from_view child_expression ((prefix++[iterator])++parameters)
          next_valuation ge locals point_temps first word CHILD_READS POINT_WORDS EVAL) as WORD; subst word.
        eapply IH with (lower:=0) (lower_code:=L.Constant 0)
          (temps:=PTree.set child_iterator (Vint Int.zero)
            (PTree.set child_bound (Vint(Int.repr(memory_source_affine_math next_valuation child_expression))) point_temps))
          (memory:=first) (after:=point_after) (final:=last); try eassumption; try reflexivity.
        -- split; assumption.
        -- apply CHILD_DOMAIN; exact RANGE.
        -- eapply affine_word_view_frame; [exact POINT_WORDS|].
           eapply temp_agree_trans; apply temp_agree_set; intro MEMBER;
             apply(NEXT_CONTROLS _ (in_or_app _ _ _ (or_introl MEMBER))); cbn; auto.
        -- eapply temp_agree_trans; [exact POINT_POINTERS|].
           eapply temp_agree_trans; apply temp_agree_set; intro MEMBER;
             apply(NEXT_CONTROLS _ (in_or_app _ _ _ (or_intror MEMBER))); cbn; auto.
        -- split; [apply PTree.gss|rewrite PTree.gso by congruence; apply PTree.gss].
    + exact SOURCE.
Qed.
End DECODE.
Print Assumptions affine_nest_source_decode.
