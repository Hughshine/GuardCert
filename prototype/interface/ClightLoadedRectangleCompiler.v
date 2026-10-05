From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST Errors Smallstep.
From compcert.cfrontend Require Import Ctypes Csyntax Csem Clight ClightBigstep.
From compcert.x86 Require Import Asm.
From Guard Require Import ClightGuard ClightCondition ClightSyntaxEquality ClightStraightLine ClightRegionProgress
  ClightFrontendRegion ClightFrontendLoopProtocol ClightTempFrame ClightRectangularStore ClightRectangularGuard ClightRectangularLoops
  ClightRectangularSelector.
From GuardInterface Require Import ClightRegionBoundary ClightReadonlyRewrite ClightReadonlyProjectedCompiler ClightReadonlyProjectedLoopRule
  ClightLoadedBoundCompiler ClightLoadedMatrixSyntax ClightLoadedRectangleRow ClightLoadedRectangleGuard ClightLoadedRectangleForward.
Import ListNotations.
Set Implicit Arguments.

(** Reuse only the untrusted rectangular shape proposer. The certificate
    below checks the real memory-bound source and every relevant AST field. *)
Definition propose_loaded_rectangle source : option rectangle_description :=
  match propose_loaded_bound source with
  | Some (row,bound,outer_body) =>
    propose_rectangle_description (frontend_counted_loop row bound outer_body)
  | None => None end.
Definition loaded_rectangle_described_source d :=
  loaded_rectangle_source (rectangle_row d) (rectangle_bound d) (rectangle_described_outer_body d).
Record loaded_rectangle_certificate source d := LoadedRectangleCertificate {
  loaded_rectangle_source_bound : source = loaded_rectangle_described_source d;
  loaded_rectangle_body_bound : flatten_region (rectangle_inner_body d) =
    [rect_store (described_shape d) (described_array d) (rectangle_row d) (rectangle_column d)];
  loaded_rectangle_outer_bound : flatten_region (rectangle_described_outer_body d) =
    [rectangle_reset (rectangle_column d);
      frontend_counted_loop (rectangle_column d) (rectangle_inner_bound d) (rectangle_inner_body d)];
  loaded_rectangle_row_bound : rectangle_row d <> rectangle_bound d;
  loaded_rectangle_row_column : rectangle_row d <> rectangle_column d;
  loaded_rectangle_bound_column : rectangle_bound d <> rectangle_column d;
  loaded_rectangle_row_columns : rectangle_row d <> rectangle_inner_bound d;
  loaded_rectangle_column_columns : rectangle_column d <> rectangle_inner_bound d;
  loaded_rectangle_layout_bound : rectangle_layout_valid (described_shape d)
}.
Definition check_loaded_rectangle source d : option (loaded_rectangle_certificate source d).
Proof.
  destruct (statement_eq source (loaded_rectangle_described_source d)) as [SOURCE|]; [|exact None].
  destruct (list_eq_dec statement_eq (flatten_region (rectangle_inner_body d))
    [rect_store (described_shape d) (described_array d) (rectangle_row d) (rectangle_column d)]) as [BODY|]; [|exact None].
  destruct (list_eq_dec statement_eq (flatten_region (rectangle_described_outer_body d))
    [rectangle_reset (rectangle_column d);
      frontend_counted_loop (rectangle_column d) (rectangle_inner_bound d) (rectangle_inner_body d)]) as [OUTER|]; [|exact None].
  destruct (peq (rectangle_row d) (rectangle_bound d)) as [|RQ]; [exact None|].
  destruct (peq (rectangle_row d) (rectangle_column d)) as [|RC]; [exact None|].
  destruct (peq (rectangle_bound d) (rectangle_column d)) as [|QC]; [exact None|].
  destruct (peq (rectangle_row d) (rectangle_inner_bound d)) as [|RM]; [exact None|].
  destruct (peq (rectangle_column d) (rectangle_inner_bound d)) as [|CM]; [exact None|].
  destruct (rectangle_layout_check (described_shape d)) eqn:LAYOUT; [|exact None].
  exact (Some (@LoadedRectangleCertificate source d SOURCE BODY OUTER RQ RC QC RM CM
    (@rectangle_layout_check_sound (described_shape d) LAYOUT))).
Defined.
Definition loaded_rectangle_rule live source d (CERT : loaded_rectangle_certificate source d) cache
  (CR : cache <> rectangle_row d) (CQ : cache <> rectangle_bound d) (CC : cache <> rectangle_column d)
  (CM : cache <> rectangle_inner_bound d) (FRESH : ~ In cache live) : readonly_projected_clight_rule live source.
Proof.
  rewrite (loaded_rectangle_source_bound CERT); unfold loaded_rectangle_described_source.
  apply readonly_projected_forward_loop_rule with
    (candidate := loaded_rectangle_candidate (described_shape d) (described_array d) (rectangle_row d) (rectangle_bound d)
      (rectangle_column d) (rectangle_inner_bound d) cache)
    (guard := @loaded_rectangle_generated_tree (described_shape d) (loaded_rectangle_layout_bound CERT)
      (described_array d) (rectangle_row d) (rectangle_bound d) (rectangle_column d) (rectangle_inner_bound d)
      (rectangle_inner_body d) (rectangle_described_outer_body d)
      (loaded_rectangle_row_bound CERT) (loaded_rectangle_row_column CERT) (loaded_rectangle_bound_column CERT)
      (loaded_rectangle_row_columns CERT) (loaded_rectangle_column_columns CERT)
      (loaded_rectangle_body_bound CERT) (loaded_rectangle_outer_bound CERT))
    (domain := loaded_rectangle_domain (rectangle_row d) (rectangle_bound d) (rectangle_described_outer_body d))
    (premise := loaded_rectangle_property (described_shape d) (described_array d) (rectangle_row d) (rectangle_bound d) (rectangle_inner_bound d))
    (writes := [rectangle_row d;rectangle_column d]).
  - exact (@loaded_rectangle_writes (described_shape d) (described_array d) (rectangle_row d) (rectangle_bound d)
      (rectangle_column d) (rectangle_inner_bound d) (rectangle_inner_body d) (rectangle_described_outer_body d)
      (loaded_rectangle_body_bound CERT) (loaded_rectangle_outer_bound CERT)).
  - exact (@loaded_rectangle_source_quiet (described_shape d) (described_array d) (rectangle_row d) (rectangle_bound d)
      (rectangle_column d) (rectangle_inner_bound d) (rectangle_inner_body d) (rectangle_described_outer_body d)
      (loaded_rectangle_body_bound CERT) (loaded_rectangle_outer_bound CERT)).
  - reflexivity.
  - intro temps; exact (@loaded_rectangle_generated_condition (described_shape d) (loaded_rectangle_layout_bound CERT)
      (adapter_entry temps) _ (boundary_observe (public_exit_ports live))
      (described_array d) (rectangle_row d) (rectangle_bound d) (rectangle_column d) (rectangle_inner_bound d)
      (rectangle_inner_body d) (rectangle_described_outer_body d)
      (loaded_rectangle_row_bound CERT) (loaded_rectangle_row_column CERT) (loaded_rectangle_bound_column CERT)
      (loaded_rectangle_row_columns CERT) (loaded_rectangle_column_columns CERT)
      (loaded_rectangle_body_bound CERT) (loaded_rectangle_outer_bound CERT)).
  - intros temps entry observed DOMAIN PREMISE SOURCE.
    exact (@loaded_rectangle_forward (described_shape d) (loaded_rectangle_layout_bound CERT) (adapter_entry temps) live
      (described_array d) (rectangle_row d) (rectangle_bound d) (rectangle_column d) (rectangle_inner_bound d) cache
      (rectangle_inner_body d) (rectangle_described_outer_body d) entry observed
      (loaded_rectangle_row_bound CERT) (loaded_rectangle_row_column CERT) (loaded_rectangle_bound_column CERT)
      (loaded_rectangle_row_columns CERT) (loaded_rectangle_column_columns CERT) CR CQ CC CM FRESH
      (loaded_rectangle_body_bound CERT) (loaded_rectangle_outer_bound CERT) DOMAIN PREMISE SOURCE).
  - intros temps p e le m le' m' SOURCE.
    exact (@loaded_rectangle_domain_from_source (described_shape d) (adapter_entry temps) (Clight.globalenv p) e le m
      (described_array d) (rectangle_row d) (rectangle_bound d) (rectangle_column d) (rectangle_inner_bound d)
      (rectangle_inner_body d) (rectangle_described_outer_body d) le' m'
      (loaded_rectangle_body_bound CERT) (loaded_rectangle_outer_bound CERT) SOURCE).
Defined.
Definition choose_loaded_rectangle live (pool : list (ident * type)) source : option (readonly_projected_clight_rule live source).
Proof.
  destruct pool as [|[cache ty] pool]; [exact None|].
  destruct (in_dec peq cache live) as [|FRESH]; [exact None|].
  destruct (propose_loaded_rectangle source) as [d|]; [|exact None].
  (** This user pass caps statically expanded checks, not the framework theorem. *)
  destruct (Z.leb (rectangle_extent (described_shape d)) 256) eqn:SIZE; [|exact None].
  destruct (check_loaded_rectangle source d) as [CERT|]; [|exact None].
  (** Include early-success exits, not only the deepest successful paths.
      For k >= 2, 1+k+...+k^n <= 2*k^n-1. *)
  destruct (Z.leb (2 * Z.pow (rectangle_stride (described_shape d) + 1)
    (rectangle_outer_limit (described_shape d)) - 1) 256) eqn:LEAVES; [|exact None].
  destruct (peq cache (rectangle_row d)) as [|CR]; [exact None|].
  destruct (peq cache (rectangle_bound d)) as [|CQ]; [exact None|].
  destruct (peq cache (rectangle_column d)) as [|CC]; [exact None|].
  destruct (peq cache (rectangle_inner_bound d)) as [|CM]; [exact None|].
  exact (Some (@loaded_rectangle_rule live source d CERT cache CR CQ CC CM FRESH)).
Defined.
Definition compile_loaded_rectangles := compile_projected_readonly choose_loaded_rectangle loaded_nested_supported 1.
Theorem compile_loaded_rectangles_correct p target : compile_loaded_rectangles p = OK target ->
  backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof. apply compile_projected_readonly_correct, loaded_nested_supported_sound. Qed.
Print Assumptions loaded_rectangle_rule.
Print Assumptions choose_loaded_rectangle.
Print Assumptions compile_loaded_rectangles_correct.
