From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib Integers.
From compcert.common Require Import AST Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightSyntaxEquality ClightTempFrame ClightNoWrap ClightCountedLoop
  ClightRegionProgress ClightStructuredProgress ClightStraightLine.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryAffineSourceExpressions
  GuardMemoryRecursiveSource GuardMemoryDynamicTensorBackend GuardMemoryMultiTensorSequence
  GuardMemoryMultiTensorSourceCapabilities.
From GuardInterface Require Import ClightLoopAdministrative ClightTensorRegionPackage
  ClightTensorBoxGuard ClightTensorCompleteGuard ClightMultiTensorDataSource ClightMultiTensorCompleteGuard ClightMultiTensorDataPackage.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Source syntax remains untrusted input. Only a real nested loop preceded
    by its exact reset is proposed as a child; a two-assignment body is a leaf.
    The independent source equality and shape checks still certify the result. *)
Fixpoint multi_tensor_propose_nest fuel source : option memory_source_nest :=
  match fuel with
  | O => None
  | S rest => match checked_structured_loop source with
    | Some loop => if described_frontend loop then
      let leaf := MemorySourceAxis (described_iterator loop) (described_bound loop) (described_body loop)
        (MemorySourceLeaf (described_body loop)) in
      match flatten_region (described_body loop) with
      | [reset;next] => match checked_structured_loop next with
        | Some child => if statement_eq reset (ClightRectangularLoops.rectangle_reset (described_iterator child)) then
          match multi_tensor_propose_nest rest next with
          | Some nested => Some (MemorySourceAxis (described_iterator loop) (described_bound loop)
            (described_body loop) nested)
          | None => None end
          else Some leaf
        | None => Some leaf end
      | _ => Some leaf end
      else None
    | None => Some (MemorySourceLeaf source) end
  end.

Definition check_multi_tensor_region_source source (description : multi_tensor_region_description) :
    option (multi_tensor_region_package source).
Proof.
  destruct (multi_tensor_propose_nest (progress_syntax_size (trim_loop_skips source)) (trim_loop_skips source))
    as [nest|]; [|exact None].
  destruct (statement_eq (trim_loop_skips source) (memory_nest_source nest)) as [SOURCE|]; [|exact None].
  destruct (describe_multi_tensor_body (mtr_dimensions description) (memory_nest_iterators nest ++ mtr_scalars description)
    (memory_nest_leaf nest) (mtr_assignments description)) as [items|] eqn:ITEMS; [|exact None].
  pose proof (@describe_multi_tensor_body_exact (mtr_dimensions description)
    (memory_nest_iterators nest ++ mtr_scalars description) (memory_nest_leaf nest)
    (mtr_assignments description) items ITEMS) as BODY.
  destruct (list_eq_dec statement_eq (map mt_statement items) []) as [EMPTY|NONEMPTY]; [exact None|].
  destruct (tensor_nest_shapes_dec nest) as [SHAPES|]; [|exact None].
  destruct (tensor_unique (memory_nest_iterators nest ++ mtr_scalars description)) eqn:UNIQUE; [|exact None].
  destruct (tensor_disjoint (memory_nest_iterators nest) (memory_nest_bounds nest)) eqn:FRESH; [|exact None].
  destruct (tensor_disjoint (memory_nest_iterators nest) (multi_tensor_body_pointers items ++
    tensor_dimension_registers (mtr_dimensions description) ++ mtr_scalars description)) eqn:PROTECTED; [|exact None].
  destruct (multi_tensor_scalar_use_check (mtr_scalars description) items) eqn:USED; [|exact None].
  destruct (tensor_subset (tensor_dimension_registers (mtr_dimensions description))
    (memory_nest_bounds nest ++ tensor_dimension_registers (tl (mtr_dimensions description)))) eqn:DIMENSIONS; [|exact None].
  destruct (zle Int.min_signed (mtr_cap description)) as [LOW|]; [|exact None].
  destruct (zle (mtr_cap description) Int.max_signed) as [HIGH|]; [|exact None].
  destruct (compile_tensor_box_guard
    (tensor_coordinate_layout (mtr_dimensions description) nest (mtr_scalars description))
    (mtr_profile description) (memory_nest_bounds nest) (mtr_scalars description)
    (mtr_dimensions description) (multi_tensor_body_accesses items)) as [tree|] eqn:COMPILE; [|exact None].
  destruct (structured_progress_supported source) eqn:PROGRESS; [|exact None].
  apply tensor_unique_sound in UNIQUE.
  refine (Some {|mtr_description:=description; mtr_nest:=nest; mtr_source:=SOURCE; mtr_items:=items;
    mtr_body:=BODY; mtr_shapes:=SHAPES; mtr_unique:=UNIQUE; mtr_used:=USED;
    mtr_tree:=tree; mtr_compile:=COMPILE; mtr_progress_checked:=PROGRESS|}).
  - intro EMPTY; subst items; cbn in NONEMPTY; contradiction.
  - split; [exact (@NoDup_app_remove_r _ (memory_nest_iterators nest) (mtr_scalars description) UNIQUE)|].
    apply tensor_disjoint_sound; exact FRESH.
  - apply tensor_disjoint_sound; exact PROTECTED.
  - intros identifier MEMBER; apply in_app_or; eapply tensor_subset_sound; [exact DIMENSIONS|exact MEMBER].
  - split; assumption.
Defined.

Print Assumptions check_multi_tensor_region_source.
