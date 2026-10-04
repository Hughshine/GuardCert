From Stdlib Require Import List Bool ZArith.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightTempFrame ClightTempFootprint ClightProjectedExecution ClightLoopSyntax
  ClightFrontendLoopProtocol ClightRectangularLoops.
From GuardMemory Require Import GuardMemoryTripleSource.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestShadowExit AffineNestLeafModel.
Import ListNotations.
Set Implicit Arguments.

Theorem affine_shadow_source_writes nest : writes_only(affine_nest_controls nest)(affine_shadow_source nest).
Proof.
  induction nest as [leaf|iterator bound expression body child IH]; [constructor|].
  change(writes_only(iterator::bound::affine_nest_controls child)
    (frontend_counted_loop iterator bound(affine_shadow_body child))).
  apply memory_frontend_loop_writes; [cbn; auto|].
  eapply writes_only_weaken with(small:=affine_nest_controls child); [intros identifier MEMBER; cbn; auto|].
  destruct child as [leaf|child_iterator child_bound child_expression child_body grandchild]; [constructor|].
  cbn [affine_shadow_body]; constructor.
  - constructor; cbn; auto.
  - constructor.
    + unfold rectangle_reset; constructor; cbn; auto.
    + exact IH.
Qed.

Definition affine_statement_scope_check live statement := forallb(fun identifier=>existsb(Pos.eqb identifier) live)(statement_temps statement).
Theorem affine_statement_scope_check_sound live statement : affine_statement_scope_check live statement=true -> statement_scope live statement.
Proof.
  intros CHECK identifier MEMBER; apply forallb_forall with(x:=identifier) in CHECK; [|exact MEMBER].
  apply existsb_exists in CHECK as [found [FOUND SAME]]; apply Pos.eqb_eq in SAME; subst; exact FOUND.
Qed.

Theorem affine_checked_shadow_transport nest bounds lower upper layout scalars pointers operations
  (certificate:affine_leaf_certificate(affine_nest_leaf nest) bounds lower upper layout scalars pointers operations)
  live fe ge locals temps memory after final private :
  affine_nest_shapes nest -> NoDup(affine_nest_controls nest) ->
  statement_scope live(affine_shadow_source nest) -> temp_agree live temps private ->
  exec_stmt fe ge locals temps memory(affine_nest_source nest) E0 after final Out_normal ->
  exists restored,
    exec_stmt fe ge locals private final(affine_shadow_source nest) E0 restored final Out_normal /\
    temp_agree live after restored.
Proof.
  intros SHAPES FRESH SCOPE FRAME SOURCE.
  pose proof(@affine_source_shadow_exit nest fe ge locals temps memory after final SHAPES FRESH
    (affine_leaf_normal certificate)(affine_leaf_quiet certificate)(affine_leaf_writes certificate) SOURCE final) as SHADOW.
  exact(@structured_execution_temp_transport fe ge locals temps final(affine_shadow_source nest) E0 after final Out_normal
    SHADOW live private(affine_nest_controls nest)(affine_shadow_source_writes nest) SCOPE FRAME).
Qed.
Print Assumptions affine_shadow_source_writes.
Print Assumptions affine_statement_scope_check_sound.
Print Assumptions affine_checked_shadow_transport.
