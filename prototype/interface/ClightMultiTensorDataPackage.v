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
  ClightTensorBoxGuard ClightTensorCompleteGuard ClightMultiTensorDataSource ClightMultiTensorCompleteGuard.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Record multi_tensor_region_description := MultiTensorRegionDescription {
  mtr_dimensions : list tensor_dimension_source;
  mtr_scalars : list ident;
  mtr_assignments : list multi_tensor_assignment_data;
  mtr_cap : Z;
  mtr_profile : list (Z*Z)
}.

(** This record is checker output. In particular the source user supplies no
    proof of source/model correspondence, frame, typing, or region progress. *)
Record multi_tensor_region_package (source : statement) := MultiTensorRegionPackage {
  mtr_description : multi_tensor_region_description;
  mtr_nest : memory_source_nest;
  mtr_source : trim_loop_skips source = memory_nest_source mtr_nest;
  mtr_items : list (multi_tensor_source_statement (mtr_dimensions mtr_description)
    (memory_nest_iterators mtr_nest ++ mtr_scalars mtr_description));
  mtr_body : flatten_region (memory_nest_leaf mtr_nest) = map mt_statement mtr_items;
  mtr_nonempty : mtr_items <> [];
  mtr_shapes : memory_nest_shapes mtr_nest;
  mtr_fresh : memory_nest_fresh mtr_nest;
  mtr_unique : NoDup (memory_nest_iterators mtr_nest ++ mtr_scalars mtr_description);
  mtr_protected : forall identifier, In identifier (memory_nest_iterators mtr_nest) ->
    ~ In identifier (multi_tensor_body_pointers mtr_items ++
      tensor_dimension_registers (mtr_dimensions mtr_description) ++ mtr_scalars mtr_description);
  mtr_used : multi_tensor_scalar_use_check (mtr_scalars mtr_description) mtr_items = true;
  mtr_dimension_reads : forall identifier, In identifier (tensor_dimension_registers (mtr_dimensions mtr_description)) ->
    In identifier (memory_nest_bounds mtr_nest) \/
    In identifier (tensor_dimension_registers (tl (mtr_dimensions mtr_description)));
  mtr_signed_cap : signed_range (mtr_cap mtr_description);
  mtr_tree : ClightCondition.decision_tree;
  mtr_compile : compile_tensor_box_guard
    (tensor_coordinate_layout (mtr_dimensions mtr_description) mtr_nest (mtr_scalars mtr_description))
    (mtr_profile mtr_description) (memory_nest_bounds mtr_nest) (mtr_scalars mtr_description)
    (mtr_dimensions mtr_description) (multi_tensor_body_accesses mtr_items) = Some mtr_tree;
  mtr_progress_checked : structured_progress_supported source = true
}.

Definition check_multi_tensor_region_description source (description : multi_tensor_region_description) :
    option (multi_tensor_region_package source).
Proof.
  destruct (tensor_propose_nest (progress_syntax_size (trim_loop_skips source)) (trim_loop_skips source))
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

Lemma multi_tensor_region_source_execution source (package : multi_tensor_region_package source)
    fe ge locals le memory trace after final outcome :
  exec_stmt fe ge locals le memory source trace after final outcome ->
  exec_stmt fe ge locals le memory (memory_nest_source (mtr_nest package)) trace after final outcome.
Proof.
  rewrite <- (mtr_source package);
    apply (proj2 (trim_loop_skips_equivalent fe source ge locals le memory trace after final outcome)).
Qed.

Lemma multi_tensor_region_source_writes source (package : multi_tensor_region_package source) :
  writes_only (memory_nest_iterators (mtr_nest package)) source.
Proof.
  apply trim_loop_skips_writes; rewrite (mtr_source package); apply memory_nest_source_writes;
    [apply mtr_shapes|eapply multi_tensor_sequence_writes; apply mtr_body].
Qed.

Lemma multi_tensor_region_source_quiet source (package : multi_tensor_region_package source) :
  quiet_statement source = true.
Proof.
  rewrite <- (trim_loop_skips_quiet source); rewrite (mtr_source package); apply memory_nest_source_quiet;
    [apply mtr_shapes|eapply multi_tensor_sequence_quiet; apply mtr_body].
Qed.

Theorem multi_tensor_region_source_progress source (package : multi_tensor_region_package source) :
  exists MODEL : region_progress source, True.
Proof. apply structured_progress_supported_sound; exact (mtr_progress_checked package). Qed.

Print Assumptions check_multi_tensor_region_description.
Print Assumptions multi_tensor_region_source_execution.
Print Assumptions multi_tensor_region_source_writes.
Print Assumptions multi_tensor_region_source_quiet.
Print Assumptions multi_tensor_region_source_progress.
