From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions.
Import ListNotations.
Set Implicit Arguments.

Fixpoint memory_source_affine_rename (rename : ident -> ident) expression := match expression with
| MemorySourceTemp identifier => MemorySourceTemp (rename identifier)
| MemorySourceConstant value => MemorySourceConstant value
| MemorySourceAdd first second => MemorySourceAdd (memory_source_affine_rename rename first) (memory_source_affine_rename rename second)
| MemorySourceSub first second => MemorySourceSub (memory_source_affine_rename rename first) (memory_source_affine_rename rename second)
| MemorySourceScale factor value => MemorySourceScale factor (memory_source_affine_rename rename value)
| MemorySourceScaleLeft factor value => MemorySourceScaleLeft factor (memory_source_affine_rename rename value)
end.

Lemma memory_source_affine_rename_math rename expression valuation :
  memory_source_affine_math valuation (memory_source_affine_rename rename expression) =
  memory_source_affine_math (fun identifier => valuation (rename identifier)) expression.
Proof. induction expression; cbn; congruence. Qed.

Lemma memory_source_affine_rename_reads rename expression :
  memory_source_affine_reads (memory_source_affine_rename rename expression) =
  map rename (memory_source_affine_reads expression).
Proof. induction expression; cbn; try rewrite map_app; congruence. Qed.

Theorem memory_source_affine_rename_evaluation rename expression valuation ge locals temps memory :
  (forall identifier, In identifier (memory_source_affine_reads expression) ->
    temps ! (rename identifier) = Some (Vint (Int.repr (valuation (rename identifier))))) ->
  eval_expr ge locals temps memory (memory_source_affine_code (memory_source_affine_rename rename expression))
    (Vint (Int.repr (memory_source_affine_math (fun identifier => valuation (rename identifier)) expression))).
Proof.
  intro WORDS; rewrite <- memory_source_affine_rename_math.
  apply memory_source_affine_evaluation; intros identifier MEMBER.
  rewrite memory_source_affine_rename_reads in MEMBER; apply in_map_iff in MEMBER as [original [<- MEMBER]].
  apply WORDS; exact MEMBER.
Qed.
Print Assumptions memory_source_affine_rename_math.
Print Assumptions memory_source_affine_rename_reads.
Print Assumptions memory_source_affine_rename_evaluation.
