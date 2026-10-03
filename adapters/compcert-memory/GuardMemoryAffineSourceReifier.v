From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import Values.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightSyntaxEquality.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint propose_memory_source_affine (source : expr) : option memory_source_affine :=
  match source with
  | Etempvar identifier _ => Some (MemorySourceTemp identifier)
  | Econst_int value _ => Some (MemorySourceConstant (Int.signed value))
  | Eunop Oneg value _ => match propose_memory_source_affine value with
    | Some (MemorySourceConstant value) => Some (MemorySourceConstant (-value))
    | _ => None end
  | Ebinop Oadd first second _ =>
    match propose_memory_source_affine first,propose_memory_source_affine second with
    | Some first,Some second => Some (MemorySourceAdd first second) | _,_ => None end
  | Ebinop Osub first second _ =>
    match propose_memory_source_affine first,propose_memory_source_affine second with
    | Some first,Some second => Some (MemorySourceSub first second) | _,_ => None end
  | Ebinop Omul first second _ =>
    match propose_memory_source_affine first,propose_memory_source_affine second with
    | Some value,Some (MemorySourceConstant factor) => Some (MemorySourceScale factor value)
    | Some (MemorySourceConstant factor),Some value => Some (MemorySourceScaleLeft factor value)
    | _,_ => None end
  | _ => None end.
Record memory_source_affine_description source := MemorySourceAffineDescription {
  memory_source_affine_expression : memory_source_affine;
  memory_source_affine_exact : source = memory_source_affine_code memory_source_affine_expression
}.
Definition describe_memory_source_affine source : option (memory_source_affine_description source) :=
  match propose_memory_source_affine source with
  | Some expression => match expression_eq source (memory_source_affine_code expression) with
    | left EXACT => Some (@MemorySourceAffineDescription source expression EXACT)
    | right _ => None end
  | None => None end.
Theorem memory_source_description_words source (description : memory_source_affine_description source)
  ge locals temps memory result :
  eval_expr ge locals temps memory source (Vint result) ->
  forall identifier, List.In identifier (memory_source_affine_reads (memory_source_affine_expression description)) ->
    exists word, temps ! identifier = Some (Vint word).
Proof.
  destruct description as [expression EXACT]; cbn; subst source; apply memory_source_affine_defined_words.
Qed.
Print Assumptions memory_source_description_words.
