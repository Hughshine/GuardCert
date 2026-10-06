From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightTempFrame ClightRedundantSet
  ClightLoopSyntax ClightRegionProgress.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestWords AffineNestSourceShape
  AffineNestSourceDecode AffineNestFirstDomain AffineNestFirstLeaf AffineNestLeafModel
  AffineNestBoundWords AffineNestUsedWords AffineNestGuardWords AffineNestGuardParameterCheck.
Import ListNotations.
Set Implicit Arguments.

(** Only the real first body is required. In particular this receipt does not
    assume completion of a root loop using a cached upper bound. *)
Definition affine_first_body_receipt iterator bound body
  (fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop) entry :=
  register_domain iterator entry /\ register_domain bound entry /\
  ((Int.signed (temp_word iterator (entry_temps entry)) <
    Int.signed (temp_word bound (entry_temps entry)))%Z ->
   exists after final, exec_stmt fe (entry_ge entry) (entry_env entry)
     (entry_temps entry) (entry_memory entry) body E0 after final Out_normal).

Section FIRST_BODY.
Variables iterator bound : ident.
Variable expression : memory_source_affine.
Variable body : statement.
Variable child : affine_source_nest.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variables ge : genv.
Variable locals : env.
Variable temps : temp_env.
Variable memory : mem.
Hypothesis SHAPES : affine_nest_shapes (AffineSourceAxis iterator bound expression body child).
Hypothesis FRESH : NoDup (affine_nest_controls (AffineSourceAxis iterator bound expression body child)).
Hypotheses (NORMAL : normal_statement (affine_nest_leaf child)=true)
  (QUIET : quiet_statement (affine_nest_leaf child)=true)
  (WRITES : writes_only [] (affine_nest_leaf child)).
Hypothesis RECEIPT : affine_first_body_receipt iterator bound body fe (Entry ge locals temps memory).

Theorem affine_first_body_header_domain :
  affine_first_header_domain (AffineSourceAxis iterator bound expression body child) temps.
Proof.
  destruct RECEIPT as [ROW [UPPER BODY]].
  cbn [register_domain entry_temps] in ROW,UPPER.
  cbn [affine_first_header_domain]; split; [exact ROW|split; [exact UPPER|]].
  intro ACTIVE; destruct (BODY ACTIVE) as [after [final RUN]].
  destruct SHAPES as [SHAPE CHILD_SHAPES].
  destruct (@affine_exit_fresh_child iterator bound expression body child FRESH)
    as [CHILD_FRESH REST].
  destruct child as [leaf|ci cb ce code grandchild]; [exact I|].
  destruct (@affine_exit_fresh_child ci cb ce code grandchild CHILD_FRESH)
    as [_ [_ DISTINCT]].
  destruct (@affine_child_setup_decode fe ge locals ci cb ce code body temps memory after final DISTINCT SHAPE RUN)
    as [word [EVAL SOURCE]].
  pose proof (@affine_expression_word_value ce ge locals temps memory word EVAL) as VALUE.
  split.
  - intros identifier MEMBER; eapply memory_source_affine_defined_words; eassumption.
  - rewrite <-VALUE; eapply affine_source_first_header_domain; eassumption.
Qed.

Theorem affine_first_body_leaf protected :
  (forall identifier, In identifier protected -> ~In identifier (affine_nest_controls child)) ->
  affine_first_path_active (AffineSourceAxis iterator bound expression body child) temps ->
  exists leaf_temps leaf_after leaf_final,
    temp_agree protected temps leaf_temps /\
    exec_stmt fe ge locals leaf_temps memory (affine_nest_leaf child)
      E0 leaf_after leaf_final Out_normal.
Proof.
  intros PROTECTED [ACTIVE CHILD_ACTIVE].
  destruct RECEIPT as [_ [_ BODY]]; destruct (BODY ACTIVE) as [after [final RUN]].
  destruct SHAPES as [SHAPE CHILD_SHAPES].
  destruct (@affine_exit_fresh_child iterator bound expression body child FRESH)
    as [CHILD_FRESH REST].
  destruct child as [leaf|ci cb ce code grandchild].
  - cbn [affine_nest_child_shape] in SHAPE; subst body.
    exists temps,after,final; split; [apply temp_agree_refl|exact RUN].
  - destruct (@affine_exit_fresh_child ci cb ce code grandchild CHILD_FRESH)
      as [_ [_ DISTINCT]].
    destruct (@affine_child_setup_decode fe ge locals ci cb ce code body temps memory after final DISTINCT SHAPE RUN)
      as [word [EVAL SOURCE]].
    pose proof (@affine_expression_word_value ce ge locals temps memory word EVAL) as VALUE.
    rewrite VALUE in SOURCE.
    destruct (@affine_source_first_leaf (AffineSourceAxis ci cb ce code grandchild)
      fe ge locals protected _ memory after final CHILD_SHAPES CHILD_FRESH NORMAL QUIET WRITES
      PROTECTED CHILD_ACTIVE SOURCE) as [leaf_temps [leaf_after [leaf_final [FRAME LEAF]]]].
    exists leaf_temps,leaf_after,leaf_final; split; [|exact LEAF].
    eapply temp_agree_trans; [apply affine_first_child_frame; exact PROTECTED|exact FRAME].
Qed.

Theorem affine_first_body_parameter_domains bounds lower upper layout scalars pointers operations
  (certificate : affine_leaf_certificate (affine_nest_leaf child) bounds lower upper layout scalars pointers operations)
  parameters :
  check_affine_guard_parameters (AffineSourceAxis iterator bound expression body child)
    layout scalars operations parameters=true ->
  affine_first_path_active (AffineSourceAxis iterator bound expression body child) temps ->
  Forall (fun identifier => register_domain identifier (Entry ge locals temps memory)) parameters.
Proof.
  intros CHECK ACTIVE; apply Forall_forall; intros identifier MEMBER.
  destruct (@check_affine_guard_parameters_sound _ _ _ _ _ CHECK identifier MEMBER) as [USED PRIVATE].
  pose proof affine_first_body_header_domain as HEADERS.
  destruct (Pos.eq_dec identifier bound) as [->|NOT_BOUND].
  - destruct HEADERS as [_ [WORD _]]; exact WORD.
  - destruct USED as [SAME|[BOUND_USED|LEAF_USED]]; [contradiction| |].
    + eapply affine_first_headers_used_bound_word; eassumption.
    + assert (PROTECTED : forall key, In key [identifier] -> ~In key (affine_nest_controls child)).
      { intros key [SAME|BAD]; [subst key|contradiction].
        intro BAD; apply PRIVATE; change (In identifier (iterator::affine_nest_controls child));
          right; exact BAD. }
      destruct (@affine_first_body_leaf [identifier] PROTECTED ACTIVE)
        as [leaf_temps [leaf_after [leaf_final [FRAME LEAF]]]].
      destruct (@affine_leaf_actual_used_word _ _ _ _ _ _ _ _ certificate
        fe ge locals leaf_temps memory leaf_after leaf_final identifier LEAF_USED LEAF) as [word WORD].
      exists word; cbn [entry_temps]; rewrite (FRAME identifier (or_introl eq_refl)) in WORD; exact WORD.
Qed.
End FIRST_BODY.

Print Assumptions affine_first_body_header_domain.
Print Assumptions affine_first_body_leaf.
Print Assumptions affine_first_body_parameter_domains.
