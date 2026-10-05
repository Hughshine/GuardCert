From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST Errors Smallstep.
From compcert.cfrontend Require Import Ctypes Csyntax Csem Clight ClightBigstep.
From compcert.x86 Require Import Asm.
From Guard Require Import ClightGuard ClightCondition ClightSyntaxEquality ClightStraightLine ClightRegionProgress
  ClightFrontendRegion ClightFrontendLoopProtocol ClightTempFrame ClightRectangularStore ClightRectangularGuard ClightRectangularLoops
  ClightRectangularSelector.
From GuardInterface Require Import ClightRegionBoundary ClightReadonlyRewrite ClightReadonlyProjectedCompiler ClightReadonlyProjectedLoopRule
  ClightLoadedBoundCompiler ClightLoadedBoundSyntax ClightLoadedMatrixSyntax ClightLoadedRectangleRow ClightLoadedRectangleGuard ClightLoadedRectangleForward
  ClightDualRectanglePrefix ClightDualRectangleGuard ClightDualRectangleSynthesis ClightDualRectangleForward
  ClightSharedProjectedCompiler ClightMixedLoadedProgress.
Import ListNotations.
Set Implicit Arguments.

(** Shape discovery remains untrusted; the certificate checks the original
    loaded heads, typed store, increments, reset and layout. *)
Definition propose_dual_rectangle source : option rectangle_description :=
  match propose_loaded_bound source with
  | Some (row,rows,outer) => match flatten_region outer with
    | [Sset column _; inner] => match propose_loaded_bound inner with
      | Some (_,columns,body) =>
        match propose_rectangle_description (frontend_counted_loop row rows
          (Ssequence (rectangle_reset column) (frontend_counted_loop column columns body))) with
        | Some d => Some (RectangleDescription (described_shape d) (described_array d)
            row rows column columns body outer)
        | None => None end
      | None => None end
    | _ => None end
  | None => None end.
Definition dual_rectangle_described_source d := dual_rect_source (rectangle_row d) (rectangle_bound d) (rectangle_described_outer_body d).
Record dual_rectangle_certificate source d := DualRectangleCertificate {
  dual_rectangle_source_bound : source = dual_rectangle_described_source d;
  dual_rectangle_body_bound : flatten_region (rectangle_inner_body d) =
    [rect_store (described_shape d) (described_array d) (rectangle_row d) (rectangle_column d)];
  dual_rectangle_outer_bound : flatten_region (rectangle_described_outer_body d) =
    [rectangle_reset (rectangle_column d);
      loaded_bound_loop (rectangle_column d) (rectangle_inner_bound d) (rectangle_inner_body d)];
  dual_rectangle_row_bound : rectangle_row d <> rectangle_bound d;
  dual_rectangle_row_column : rectangle_row d <> rectangle_column d;
  dual_rectangle_bound_column : rectangle_column d <> rectangle_bound d;
  dual_rectangle_row_columns : rectangle_row d <> rectangle_inner_bound d;
  dual_rectangle_column_columns : rectangle_column d <> rectangle_inner_bound d;
  dual_rectangle_layout_bound : rectangle_layout_valid (described_shape d)
}.
Definition check_dual_rectangle source d : option (dual_rectangle_certificate source d).
Proof.
  destruct (statement_eq source (dual_rectangle_described_source d)) as [SOURCE|]; [|exact None].
  destruct (list_eq_dec statement_eq (flatten_region (rectangle_inner_body d))
    [rect_store (described_shape d) (described_array d) (rectangle_row d) (rectangle_column d)]) as [BODY|]; [|exact None].
  destruct (list_eq_dec statement_eq (flatten_region (rectangle_described_outer_body d))
    [rectangle_reset (rectangle_column d);
      loaded_bound_loop (rectangle_column d) (rectangle_inner_bound d) (rectangle_inner_body d)]) as [OUTER|]; [|exact None].
  destruct (peq (rectangle_row d) (rectangle_bound d)) as [|RQ]; [exact None|].
  destruct (peq (rectangle_row d) (rectangle_column d)) as [|RC]; [exact None|].
  destruct (peq (rectangle_column d) (rectangle_bound d)) as [|QC]; [exact None|].
  destruct (peq (rectangle_row d) (rectangle_inner_bound d)) as [|RM]; [exact None|].
  destruct (peq (rectangle_column d) (rectangle_inner_bound d)) as [|CM]; [exact None|].
  destruct (rectangle_layout_check (described_shape d)) eqn:LAYOUT; [|exact None].
  exact (Some (@DualRectangleCertificate source d SOURCE BODY OUTER RQ RC QC RM CM
    (@rectangle_layout_check_sound (described_shape d) LAYOUT))).
Defined.
Definition dual_rectangle_rule live source d (CERT : dual_rectangle_certificate source d) row_cache column_cache
  (CR : row_cache <> rectangle_row d) (CQ : row_cache <> rectangle_bound d) (CC : row_cache <> rectangle_column d)
  (CM : row_cache <> rectangle_inner_bound d)
  (KR : column_cache <> rectangle_row d) (KQ : column_cache <> rectangle_bound d) (KC : column_cache <> rectangle_column d)
  (KM : column_cache <> rectangle_inner_bound d) (DISTINCT : row_cache <> column_cache)
  (FRESH : ~ In row_cache live) (FRESH2 : ~ In column_cache live) : readonly_projected_clight_rule live source.
Proof.
  rewrite (dual_rectangle_source_bound CERT); unfold dual_rectangle_described_source.
  apply readonly_projected_forward_loop_rule with
    (candidate := dual_rect_candidate (described_shape d) (described_array d) (rectangle_row d) (rectangle_bound d)
      (rectangle_column d) (rectangle_inner_bound d) row_cache column_cache)
    (guard := @dual_rect_generated_tree (described_shape d) (dual_rectangle_layout_bound CERT)
      (described_array d) (rectangle_row d) (rectangle_bound d) (rectangle_column d) (rectangle_inner_bound d)
      (rectangle_inner_body d) (rectangle_described_outer_body d)
      (dual_rectangle_row_column CERT) (dual_rectangle_row_bound CERT) (dual_rectangle_row_columns CERT)
      (dual_rectangle_bound_column CERT) (dual_rectangle_column_columns CERT)
      (dual_rectangle_body_bound CERT) (dual_rectangle_outer_bound CERT))
    (domain := dual_rect_domain (rectangle_row d) (rectangle_bound d) (rectangle_described_outer_body d))
    (premise := dual_rect_property (described_shape d) (described_array d) (rectangle_row d) (rectangle_bound d) (rectangle_inner_bound d))
    (writes := [rectangle_row d;rectangle_column d]).
  - exact (@dual_rect_source_writes (described_shape d) (described_array d) (rectangle_row d) (rectangle_bound d)
      (rectangle_column d) (rectangle_inner_bound d) (rectangle_inner_body d) (rectangle_described_outer_body d)
      (dual_rectangle_body_bound CERT) (dual_rectangle_outer_bound CERT)).
  - exact (@dual_rect_source_quiet (described_shape d) (described_array d) (rectangle_row d) (rectangle_bound d)
      (rectangle_column d) (rectangle_inner_bound d) (rectangle_inner_body d) (rectangle_described_outer_body d)
      (dual_rectangle_body_bound CERT) (dual_rectangle_outer_bound CERT)).
  - reflexivity.
  - intro temps; exact (@dual_rect_generated_condition (described_shape d) (dual_rectangle_layout_bound CERT)
      (adapter_entry temps) _ (boundary_observe (public_exit_ports live))
      (described_array d) (rectangle_row d) (rectangle_bound d) (rectangle_column d) (rectangle_inner_bound d)
      (rectangle_inner_body d) (rectangle_described_outer_body d)
      (dual_rectangle_row_column CERT) (dual_rectangle_row_bound CERT) (dual_rectangle_row_columns CERT)
      (dual_rectangle_bound_column CERT) (dual_rectangle_column_columns CERT)
      (dual_rectangle_body_bound CERT) (dual_rectangle_outer_bound CERT)).
  - intros temps entry observed DOMAIN PREMISE SOURCE.
    exact (@dual_rect_forward (described_shape d) (dual_rectangle_layout_bound CERT) (adapter_entry temps) live
      (described_array d) (rectangle_row d) (rectangle_bound d) (rectangle_column d) (rectangle_inner_bound d) row_cache column_cache
      (rectangle_inner_body d) (rectangle_described_outer_body d) entry observed
      (dual_rectangle_row_column CERT) (dual_rectangle_row_bound CERT) (dual_rectangle_row_columns CERT)
      (dual_rectangle_bound_column CERT) (dual_rectangle_column_columns CERT) CR CQ CC CM KR KQ KC KM DISTINCT FRESH FRESH2
      (dual_rectangle_body_bound CERT) (dual_rectangle_outer_bound CERT) DOMAIN PREMISE SOURCE).
  - intros temps p e le m le' m' SOURCE.
    exact (@dual_rect_domain_from_source (described_shape d) (adapter_entry temps) (Clight.globalenv p) e le m
      (described_array d) (rectangle_row d) (rectangle_bound d) (rectangle_column d) (rectangle_inner_bound d)
      (rectangle_inner_body d) (rectangle_described_outer_body d) le' m'
      (dual_rectangle_body_bound CERT) (dual_rectangle_outer_bound CERT) SOURCE).
Defined.
Definition choose_dual_rectangle live (pool : list (ident * type)) source : option (readonly_projected_clight_rule live source).
Proof.
  destruct pool as [|[row_cache ty] pool]; [exact None|].
  destruct pool as [|[column_cache ty2] pool]; [exact None|].
  destruct (in_dec peq row_cache live) as [|FRESH]; [exact None|].
  destruct (in_dec peq column_cache live) as [|FRESH2]; [exact None|].
  destruct (peq row_cache column_cache) as [|DISTINCT]; [exact None|].
  destruct (propose_dual_rectangle source) as [d|]; [|exact None].
  (** The rule theorem has no extent cap. This prototype bounds expanded
      address probes and preserves one shared candidate/fallback. *)
  destruct (Z.leb (rectangle_extent (described_shape d)) 12) eqn:SIZE; [|exact None].
  destruct (check_dual_rectangle source d) as [CERT|]; [|exact None].
  destruct (peq row_cache (rectangle_row d)) as [|CR]; [exact None|].
  destruct (peq row_cache (rectangle_bound d)) as [|CQ]; [exact None|].
  destruct (peq row_cache (rectangle_column d)) as [|CC]; [exact None|].
  destruct (peq row_cache (rectangle_inner_bound d)) as [|CM]; [exact None|].
  destruct (peq column_cache (rectangle_row d)) as [|KR]; [exact None|].
  destruct (peq column_cache (rectangle_bound d)) as [|KQ]; [exact None|].
  destruct (peq column_cache (rectangle_column d)) as [|KC]; [exact None|].
  destruct (peq column_cache (rectangle_inner_bound d)) as [|KM]; [exact None|].
  exact (Some (@dual_rectangle_rule live source d CERT row_cache column_cache CR CQ CC CM KR KQ KC KM DISTINCT FRESH FRESH2)).
Defined.
Definition compile_dual_rectangles := compile_shared_projected choose_dual_rectangle mixed_loaded_progress_supported 3.
Theorem compile_dual_rectangles_correct p target : compile_dual_rectangles p = OK target ->
  backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof. apply compile_shared_projected_correct, mixed_loaded_progress_supported_sound. Qed.
Print Assumptions dual_rectangle_rule.
Print Assumptions choose_dual_rectangle.
Print Assumptions compile_dual_rectangles_correct.
