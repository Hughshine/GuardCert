From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST Errors Smallstep.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep Csem.
From compcert.x86 Require Import Asm.
From Guard Require Import ClightGuard ClightCondition ClightSyntaxEquality ClightStraightLine ClightRegionProgress
  ClightFrontendLoopProtocol ClightTempFrame ClightRectangularStore ClightRectangularGuard ClightRectangularLoops
  ClightRectangularSelector.
From GuardInterface Require Import ClightRegionBoundary ClightReadonlyRewrite ClightReadonlyProjectedCompiler
  ClightReadonlyProjectedLoopRule ClightLoadedBoundCompiler ClightLoadedMatrixSyntax ClightRuntimeStrideBody
  ClightRuntimeStrideCompiler ClightLoadedRectangleRow ClightLoadedStrideTransport ClightLoadedStrideGuard
  ClightLoadedStrideForward ClightProbeTree ClightSharedProjectedCompiler.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition loaded_stride_source d := loaded_rectangle_source (rectangle_row (stride_rectangle d))
  (rectangle_bound (stride_rectangle d)) (rectangle_described_outer_body (stride_rectangle d)).
Record loaded_stride_certificate source d := LoadedStrideCertificate {
  loaded_stride_original : source = loaded_stride_source d;
  loaded_stride_structure : stride_certificate (stride_source d) d
}.
Definition propose_loaded_stride source :=
  match propose_loaded_bound source with Some (row,bound,outer_body) =>
    propose_stride_description (frontend_counted_loop row bound outer_body) | None => None end.
Definition check_loaded_stride source d : option (loaded_stride_certificate source d).
Proof.
  destruct (statement_eq source (loaded_stride_source d)) as [SOURCE|]; [|exact None].
  destruct (check_stride_description (stride_source d) d) as [CERT|]; [|exact None].
  exact (Some (@LoadedStrideCertificate source d SOURCE CERT)).
Defined.

Definition loaded_stride_rule live source d (CERT : loaded_stride_certificate source d) cache
  (CR : cache <> rectangle_row (stride_rectangle d)) (CQ : cache <> rectangle_bound (stride_rectangle d))
  (CC : cache <> rectangle_column (stride_rectangle d)) (CM : cache <> rectangle_inner_bound (stride_rectangle d))
  (CS : cache <> stride_parameter d) (FRESH : ~ In cache live) : readonly_projected_clight_rule live source.
Proof.
  rewrite (loaded_stride_original CERT); unfold loaded_stride_source.
  pose (SHAPE := described_shape (stride_rectangle d)).
  pose (SCERT := loaded_stride_structure CERT).
  pose (MODELS := enumerate_loaded_stride_models SHAPE).
  apply readonly_projected_forward_loop_rule with
    (candidate := loaded_stride_candidate SHAPE (described_array (stride_rectangle d)) (rectangle_row (stride_rectangle d))
      (rectangle_bound (stride_rectangle d)) (rectangle_column (stride_rectangle d)) (rectangle_inner_bound (stride_rectangle d))
      (stride_parameter d) cache)
    (guard := @loaded_stride_tree SHAPE (described_array (stride_rectangle d)) (rectangle_row (stride_rectangle d))
      (rectangle_bound (stride_rectangle d)) (rectangle_column (stride_rectangle d)) (rectangle_inner_bound (stride_rectangle d))
      (stride_parameter d) (stride_row_bound SCERT) (stride_row_column SCERT) (stride_bound_column SCERT)
      (stride_row_inner_bound SCERT) (stride_column_inner_bound SCERT) MODELS)
    (domain := loaded_stride_domain (rectangle_row (stride_rectangle d)) (rectangle_bound (stride_rectangle d))
      (rectangle_described_outer_body (stride_rectangle d)))
    (premise := @loaded_stride_property SHAPE (described_array (stride_rectangle d)) (rectangle_row (stride_rectangle d))
      (rectangle_bound (stride_rectangle d)) (rectangle_inner_bound (stride_rectangle d)) (stride_parameter d) MODELS)
    (writes := [rectangle_row (stride_rectangle d);rectangle_column (stride_rectangle d)]).
  - exact (@loaded_stride_writes SHAPE (described_array (stride_rectangle d)) (rectangle_row (stride_rectangle d))
      (rectangle_bound (stride_rectangle d)) (rectangle_column (stride_rectangle d)) (rectangle_inner_bound (stride_rectangle d))
      (stride_parameter d) (rectangle_inner_body (stride_rectangle d)) (rectangle_described_outer_body (stride_rectangle d))
      (stride_body_bound SCERT) (stride_outer_bound SCERT)).
  - exact (@loaded_stride_source_quiet SHAPE (described_array (stride_rectangle d)) (rectangle_row (stride_rectangle d))
      (rectangle_bound (stride_rectangle d)) (rectangle_column (stride_rectangle d)) (rectangle_inner_bound (stride_rectangle d))
      (stride_parameter d) (rectangle_inner_body (stride_rectangle d)) (rectangle_described_outer_body (stride_rectangle d))
      (stride_body_bound SCERT) (stride_outer_bound SCERT)).
  - reflexivity.
  - intro temps; exact (@loaded_stride_condition SHAPE (described_array (stride_rectangle d)) (rectangle_row (stride_rectangle d))
      (rectangle_bound (stride_rectangle d)) (rectangle_column (stride_rectangle d)) (rectangle_inner_bound (stride_rectangle d))
      (stride_parameter d) (rectangle_inner_body (stride_rectangle d)) (rectangle_described_outer_body (stride_rectangle d))
      (stride_row_bound SCERT) (stride_row_column SCERT) (stride_bound_column SCERT) (stride_row_inner_bound SCERT)
      (stride_column_inner_bound SCERT) (stride_parameter_row SCERT) (stride_parameter_column SCERT)
      (stride_body_bound SCERT) (stride_outer_bound SCERT) (adapter_entry temps) _ (boundary_observe (public_exit_ports live)) MODELS).
  - intros temps entry observed DOMAIN PREMISE SOURCE.
    exact (@loaded_stride_forward SHAPE (adapter_entry temps) live (described_array (stride_rectangle d)) (rectangle_row (stride_rectangle d))
      (rectangle_bound (stride_rectangle d)) (rectangle_column (stride_rectangle d)) (rectangle_inner_bound (stride_rectangle d))
      (stride_parameter d) cache (rectangle_inner_body (stride_rectangle d)) (rectangle_described_outer_body (stride_rectangle d)) MODELS entry observed
      (stride_row_bound SCERT) (stride_row_column SCERT) (stride_bound_column SCERT) (stride_row_inner_bound SCERT)
      (stride_column_inner_bound SCERT) (stride_parameter_row SCERT) (stride_parameter_column SCERT)
      CR CQ CC CM CS FRESH (stride_body_bound SCERT) (stride_outer_bound SCERT) DOMAIN PREMISE SOURCE).
  - intros temps p e le m le' m' SOURCE.
    exact (@loaded_stride_domain_from_source SHAPE (adapter_entry temps) (Clight.globalenv p) e le m
      (described_array (stride_rectangle d)) (rectangle_row (stride_rectangle d)) (rectangle_bound (stride_rectangle d))
      (rectangle_column (stride_rectangle d)) (rectangle_inner_bound (stride_rectangle d)) (stride_parameter d)
      (rectangle_inner_body (stride_rectangle d)) (rectangle_described_outer_body (stride_rectangle d)) le' m'
      (stride_body_bound SCERT) (stride_outer_bound SCERT) SOURCE).
Defined.

Fixpoint loaded_stride_tree_size tree : nat :=
  match tree with Decision _ => 1%nat | Test _ yes no => S (loaded_stride_tree_size yes + loaded_stride_tree_size no) end.
Definition choose_loaded_stride live (pool : list (ident * type)) source : option (readonly_projected_clight_rule live source).
Proof.
  destruct pool as [|[cache ty] pool]; [exact None|].
  destruct (in_dec peq cache live) as [|FRESH]; [exact None|].
  destruct (propose_loaded_stride source) as [d|]; [|exact None].
  (** Enumerate all checked layouts of a small fixed array. This is a user
      code-generation budget, not a restriction of the framework theorem. *)
  destruct (Z.leb (rectangle_extent (described_shape (stride_rectangle d))) 12) eqn:SIZE; [|exact None].
  destruct (check_loaded_stride source d) as [CERT|]; [|exact None].
  destruct (peq cache (rectangle_row (stride_rectangle d))) as [|CR]; [exact None|].
  destruct (peq cache (rectangle_bound (stride_rectangle d))) as [|CQ]; [exact None|].
  destruct (peq cache (rectangle_column (stride_rectangle d))) as [|CC]; [exact None|].
  destruct (peq cache (rectangle_inner_bound (stride_rectangle d))) as [|CM]; [exact None|].
  destruct (peq cache (stride_parameter d)) as [|CS]; [exact None|].
  pose (rule := simplified_projected_rule (@loaded_stride_rule live source d CERT cache CR CQ CC CM CS FRESH)).
  destruct (Nat.leb (loaded_stride_tree_size (projected_guard rule)) 4096) eqn:NODES; [|exact None].
  exact (Some rule).
Defined.
Definition compile_loaded_strides := compile_shared_projected choose_loaded_stride loaded_nested_supported 2.
Theorem compile_loaded_strides_correct p target : compile_loaded_strides p = OK target ->
  backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof. apply compile_shared_projected_correct, loaded_nested_supported_sound. Qed.

Print Assumptions loaded_stride_rule.
Print Assumptions choose_loaded_stride.
Print Assumptions compile_loaded_strides_correct.
