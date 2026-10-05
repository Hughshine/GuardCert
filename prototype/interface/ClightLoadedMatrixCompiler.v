From Stdlib Require Import List Bool.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST Errors Smallstep.
From compcert.cfrontend Require Import Ctypes Csyntax Csem Clight ClightBigstep.
From compcert.x86 Require Import Asm.
From Guard Require Import ClightGuard ClightCondition ClightSyntaxEquality ClightStraightLine ClightRegionProgress
  ClightFrontendRegion ClightFrontendLoopProtocol ClightTempFrame ClightMatrixStore ClightMatrixLoops ClightMatrixSelector.
From GuardInterface Require Import ClightRegionBoundary ClightReadonlyRewrite ClightReadonlyProjectedCompiler ClightReadonlyProjectedLoopRule
  ClightLoadedBoundCompiler ClightLoadedMatrixSyntax ClightLoadedMatrixGuard ClightLoadedMatrixLoop.
Import ListNotations.
Set Implicit Arguments.

Definition propose_loaded_matrix source : option matrix_description :=
  match propose_loaded_bound source with
  | Some (row,bound,outer_body) => match flatten_region outer_body with
    | [Sset column _; inner_loop] => match propose_frontend_shape inner_loop with
      | Some (_,columns,body) => match flatten_region body with
        | [Sassign (Ederef (Ebinop _ (Evar array _) _ _) _) _] =>
          Some (MatrixDescription array row bound column columns body outer_body)
        | _ => None end
      | None => None end
    | _ => None end
  | None => None end.
Definition loaded_matrix_described_source d := loaded_matrix_source (matrix_row d) (matrix_bound d) (matrix_outer_body d).
Record loaded_matrix_certificate source d := LoadedMatrixCertificate {
  loaded_matrix_source_bound : source = loaded_matrix_described_source d;
  loaded_matrix_body_bound : flatten_region (matrix_inner_body d) =
    [matrix_store (described_array d) (matrix_row d) (matrix_column d)];
  loaded_matrix_outer_bound : flatten_region (matrix_outer_body d) =
    [matrix_reset (matrix_column d); frontend_counted_loop (matrix_column d) (matrix_inner_bound d) (matrix_inner_body d)];
  loaded_matrix_row_column : matrix_row d <> matrix_column d;
  loaded_matrix_row_bound : matrix_row d <> matrix_bound d;
  loaded_matrix_column_bound : matrix_column d <> matrix_bound d;
  loaded_matrix_row_columns : matrix_row d <> matrix_inner_bound d;
  loaded_matrix_column_columns : matrix_column d <> matrix_inner_bound d
}.
Definition check_loaded_matrix source d : option (loaded_matrix_certificate source d).
Proof.
  destruct (statement_eq source (loaded_matrix_described_source d)) as [SOURCE|]; [|exact None].
  destruct (list_eq_dec statement_eq (flatten_region (matrix_inner_body d))
    [matrix_store (described_array d) (matrix_row d) (matrix_column d)]) as [BODY|]; [|exact None].
  destruct (list_eq_dec statement_eq (flatten_region (matrix_outer_body d))
    [matrix_reset (matrix_column d); frontend_counted_loop (matrix_column d) (matrix_inner_bound d) (matrix_inner_body d)])
    as [OUTER|]; [|exact None].
  destruct (peq (matrix_row d) (matrix_column d)) as [|RC]; [exact None|].
  destruct (peq (matrix_row d) (matrix_bound d)) as [|RQ]; [exact None|].
  destruct (peq (matrix_column d) (matrix_bound d)) as [|CQ]; [exact None|].
  destruct (peq (matrix_row d) (matrix_inner_bound d)) as [|RM]; [exact None|].
  destruct (peq (matrix_column d) (matrix_inner_bound d)) as [|CM]; [exact None|].
  exact (Some (@LoadedMatrixCertificate source d SOURCE BODY OUTER RC RQ CQ RM CM)).
Defined.
Definition loaded_matrix_rule live source d (CERT : loaded_matrix_certificate source d) cache
  (CR : cache <> matrix_row d) (CQ : cache <> matrix_bound d) (CC : cache <> matrix_column d)
  (CM : cache <> matrix_inner_bound d) (FRESH : ~ In cache live) : readonly_projected_clight_rule live source.
Proof.
  rewrite (loaded_matrix_source_bound CERT); unfold loaded_matrix_described_source.
  apply readonly_projected_forward_loop_rule with
    (candidate := loaded_matrix_candidate (matrix_row d) (matrix_bound d) (matrix_column d)
      (matrix_inner_bound d) (described_array d) cache)
    (guard := loaded_matrix_tree (matrix_row d) (matrix_bound d) (matrix_inner_bound d) (described_array d))
    (domain := loaded_matrix_domain (matrix_row d) (matrix_bound d) (matrix_outer_body d))
    (premise := loaded_matrix_property (matrix_row d) (matrix_bound d) (matrix_inner_bound d) (described_array d))
    (writes := [matrix_row d;matrix_column d]).
  - exact (@loaded_matrix_writes (described_array d) (matrix_row d) (matrix_bound d) (matrix_column d)
      (matrix_inner_bound d) (matrix_inner_body d) (matrix_outer_body d)
      (loaded_matrix_body_bound CERT) (loaded_matrix_outer_bound CERT)).
  - exact (@loaded_matrix_source_quiet (described_array d) (matrix_row d) (matrix_bound d) (matrix_column d)
      (matrix_inner_bound d) (matrix_inner_body d) (matrix_outer_body d)
      (loaded_matrix_body_bound CERT) (loaded_matrix_outer_bound CERT)).
  - reflexivity.
  - intro temps; exact (@loaded_matrix_condition (adapter_entry temps) _ (boundary_observe (public_exit_ports live))
      (described_array d) (matrix_row d) (matrix_bound d) (matrix_column d) (matrix_inner_bound d)
      (matrix_inner_body d) (matrix_outer_body d) (loaded_matrix_row_column CERT) (loaded_matrix_row_bound CERT)
      (loaded_matrix_column_bound CERT) (loaded_matrix_row_columns CERT) (loaded_matrix_column_columns CERT)
      (loaded_matrix_body_bound CERT) (loaded_matrix_outer_bound CERT)).
  - intros temps entry observed DOMAIN PREMISE SOURCE.
    exact (@loaded_matrix_forward (adapter_entry temps) live (described_array d) (matrix_row d) (matrix_bound d)
      (matrix_column d) (matrix_inner_bound d) cache (matrix_inner_body d) (matrix_outer_body d) entry observed
      (loaded_matrix_row_column CERT) (loaded_matrix_row_bound CERT) (loaded_matrix_row_columns CERT)
      (loaded_matrix_column_bound CERT) (loaded_matrix_column_columns CERT) CR CQ CC CM FRESH
      (loaded_matrix_body_bound CERT) (loaded_matrix_outer_bound CERT) DOMAIN PREMISE SOURCE).
  - intros temps p e le m le' m' SOURCE.
    exact (@loaded_matrix_domain_from_source (adapter_entry temps) (Clight.globalenv p) e le m
      (described_array d) (matrix_row d) (matrix_bound d) (matrix_column d) (matrix_inner_bound d)
      (matrix_inner_body d) (matrix_outer_body d) le' m' (loaded_matrix_body_bound CERT)
      (loaded_matrix_outer_bound CERT) SOURCE).
Defined.
Definition choose_loaded_matrix live (pool : list (ident * type)) source : option (readonly_projected_clight_rule live source).
Proof.
  destruct pool as [|[cache ty] pool]; [exact None|].
  destruct (in_dec peq cache live) as [|FRESH]; [exact None|].
  destruct (propose_loaded_matrix source) as [d|]; [|exact None].
  destruct (check_loaded_matrix source d) as [CERT|]; [|exact None].
  destruct (peq cache (matrix_row d)) as [|CR]; [exact None|].
  destruct (peq cache (matrix_bound d)) as [|CQ]; [exact None|].
  destruct (peq cache (matrix_column d)) as [|CC]; [exact None|].
  destruct (peq cache (matrix_inner_bound d)) as [|CM]; [exact None|].
  exact (Some (@loaded_matrix_rule live source d CERT cache CR CQ CC CM FRESH)).
Defined.
Definition compile_loaded_matrices := compile_projected_readonly choose_loaded_matrix loaded_nested_supported 1.
Theorem compile_loaded_matrices_correct p target : compile_loaded_matrices p = OK target ->
  backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof. apply compile_projected_readonly_correct, loaded_nested_supported_sound. Qed.
Print Assumptions loaded_matrix_rule.
Print Assumptions choose_loaded_matrix.
Print Assumptions compile_loaded_matrices_correct.
