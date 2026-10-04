From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Coqlib Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightNoWrap.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions GuardMemoryAffineRenaming.
From GuardAffineNest Require Import AffineNestExit AffineNestFirstDomain.
Import ListNotations.
Set Implicit Arguments.

Definition affine_renamed_view registers rename (source target : temp_env) :=
  forall identifier, In identifier registers -> target!(rename identifier)=source!identifier.
Definition affine_rename_injective (registers : list ident) (rename : ident -> ident) :=
  forall first second, In first registers -> In second registers -> rename first=rename second -> first=second.

Lemma affine_renamed_view_weaken small big rename source target :
  (forall identifier, In identifier small -> In identifier big) ->
  affine_renamed_view big rename source target -> affine_renamed_view small rename source target.
Proof. intros SUBSET VIEW identifier MEMBER; apply VIEW,SUBSET; exact MEMBER. Qed.

Lemma affine_renamed_view_set registers rename source target identifier value :
  affine_rename_injective registers rename -> In identifier registers ->
  affine_renamed_view registers rename source target ->
  affine_renamed_view registers rename (PTree.set identifier value source) (PTree.set (rename identifier) value target).
Proof.
  intros UNIQUE MEMBER VIEW key KEY; destruct(peq key identifier) as [->|OTHER].
  - rewrite !PTree.gss; reflexivity.
  - rewrite !PTree.gso; [apply VIEW; exact KEY|exact OTHER|].
    intro SAME; apply OTHER; eapply UNIQUE; eassumption.
Qed.

Lemma affine_renamed_view_extend_set current registers rename source target identifier value :
  affine_rename_injective registers rename ->
  (forall key, In key current -> In key registers) -> In identifier registers ->
  affine_renamed_view current rename source target ->
  affine_renamed_view (current++[identifier]) rename
    (PTree.set identifier value source) (PTree.set(rename identifier) value target).
Proof.
  intros UNIQUE COVERAGE MEMBER VIEW key KEY; destruct(peq key identifier) as [->|OTHER].
  - rewrite !PTree.gss; reflexivity.
  - assert (CURRENT:In key current).
    { apply in_app_or in KEY; destruct KEY as [KEY|KEY]; [exact KEY|cbn in KEY; intuition congruence]. }
    rewrite !PTree.gso; [apply VIEW; exact CURRENT|exact OTHER|].
    intro SAME; apply OTHER; eapply UNIQUE; [apply COVERAGE; exact CURRENT|exact MEMBER|exact SAME].
Qed.

Lemma affine_expression_math_frame expression first second :
  (forall identifier, In identifier(memory_source_affine_reads expression) -> first identifier=second identifier) ->
  memory_source_affine_math first expression=memory_source_affine_math second expression.
Proof.
  induction expression; intro VIEW; cbn [memory_source_affine_math].
  - apply VIEW; cbn; auto.
  - reflexivity.
  - f_equal; [apply IHexpression1|apply IHexpression2]; intros identifier MEMBER; apply VIEW,in_or_app; auto.
  - f_equal; [apply IHexpression1|apply IHexpression2]; intros identifier MEMBER; apply VIEW,in_or_app; auto.
  - f_equal; apply IHexpression; exact VIEW.
  - f_equal; apply IHexpression; exact VIEW.
Qed.

Theorem affine_renamed_bound_evaluation expression registers rename ge locals source target memory :
  (forall identifier, In identifier(memory_source_affine_reads expression) -> In identifier registers) ->
  affine_expression_word_domain expression source -> affine_renamed_view registers rename source target ->
  eval_expr ge locals target memory (memory_source_affine_code(memory_source_affine_rename rename expression))
    (Vint(Int.repr(memory_source_affine_math (affine_word_valuation source) expression))).
Proof.
  intros READS WORDS VIEW.
  assert (MATH:memory_source_affine_math (affine_word_valuation target)
    (memory_source_affine_rename rename expression)=
    memory_source_affine_math (affine_word_valuation source) expression).
  { rewrite memory_source_affine_rename_math; apply affine_expression_math_frame.
    intros identifier MEMBER; unfold affine_word_valuation,temp_word; rewrite VIEW by (apply READS; exact MEMBER); reflexivity. }
  rewrite <-MATH; apply memory_source_affine_evaluation.
  intros identifier MEMBER; rewrite memory_source_affine_rename_reads in MEMBER.
  apply in_map_iff in MEMBER as [original [<- MEMBER]].
  destruct(WORDS original MEMBER) as [word WORD].
  rewrite VIEW by (apply READS; exact MEMBER); rewrite WORD.
  unfold affine_word_valuation,temp_word; rewrite VIEW by (apply READS; exact MEMBER); rewrite WORD,Int.repr_signed; reflexivity.
Qed.
Print Assumptions affine_renamed_view_set.
Print Assumptions affine_expression_math_frame.
Print Assumptions affine_renamed_bound_evaluation.
