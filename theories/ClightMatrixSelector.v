From Stdlib Require Import List ZArith.
From compcert.lib Require Import Coqlib Integers.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import CompCertIndexSchedule ClightSyntaxEquality ClightRegionRewrite ClightRegionRule
  ClightStraightLine ClightFrontendLoopProtocol ClightFrontendRegion
  ClightMatrixStore ClightMatrixLoops ClightMatrixRegion.
Import ListNotations.
Set Implicit Arguments.

Record matrix_description := MatrixDescription {
  described_array : ident;
  matrix_row : ident;
  matrix_bound : ident;
  matrix_column : ident;
  matrix_inner_bound : ident;
  matrix_inner_body : statement;
  matrix_outer_body : statement
}.
Definition matrix_described_source d := frontend_counted_loop (matrix_row d) (matrix_bound d) (matrix_outer_body d).
Definition matrix_described_target d :=
  matrix_interchanged (matrix_row d) (matrix_bound d) (matrix_column d) (matrix_inner_bound d) (described_array d).

(** A proposal is untrusted. Full AST equality and identifier/frame checks
    below bind every expression and every control component to the proof. *)
Definition propose_matrix_description source : option matrix_description :=
  match propose_frontend_shape source with
  | Some (row,bound,outer_body) => match flatten_region outer_body with
    | [Sset column _; inner_loop] => match propose_frontend_shape inner_loop with
      | Some (_,inner_bound,inner_body) => match flatten_region inner_body with
        | [Sassign (Ederef (Ebinop _ (Evar array _) _ _) _) _] =>
            Some (MatrixDescription array row bound column inner_bound inner_body outer_body)
        | _ => None end
      | None => None end
    | _ => None end
  | None => None end.

Record matrix_certificate source d := MatrixCertificate {
  matrix_source_bound : source = matrix_described_source d;
  matrix_body_bound : flatten_region (matrix_inner_body d) =
    [matrix_store (described_array d) (matrix_row d) (matrix_column d)];
  matrix_outer_bound : flatten_region (matrix_outer_body d) =
    [matrix_reset (matrix_column d);
      frontend_counted_loop (matrix_column d) (matrix_inner_bound d) (matrix_inner_body d)];
  matrix_distinct_row_bound : matrix_row d <> matrix_bound d;
  matrix_distinct_row_column : matrix_row d <> matrix_column d;
  matrix_distinct_bound_column : matrix_bound d <> matrix_column d;
  matrix_distinct_row_inner_bound : matrix_row d <> matrix_inner_bound d;
  matrix_distinct_column_inner_bound : matrix_column d <> matrix_inner_bound d;
  matrix_schedule_bound : check_index_schedule row_index_order column_index_order = true
}.

Definition check_matrix_description source d : option (matrix_certificate source d).
Proof.
  destruct (statement_eq source (matrix_described_source d)) as [SOURCE|]; [|exact None].
  destruct (list_eq_dec statement_eq (flatten_region (matrix_inner_body d))
    [matrix_store (described_array d) (matrix_row d) (matrix_column d)]) as [BODY|]; [|exact None].
  destruct (list_eq_dec statement_eq (flatten_region (matrix_outer_body d))
    [matrix_reset (matrix_column d);
      frontend_counted_loop (matrix_column d) (matrix_inner_bound d) (matrix_inner_body d)]) as [OUTER|]; [|exact None].
  destruct (peq (matrix_row d) (matrix_bound d)) as [|RN]; [exact None|].
  destruct (peq (matrix_row d) (matrix_column d)) as [|RC]; [exact None|].
  destruct (peq (matrix_bound d) (matrix_column d)) as [|NC]; [exact None|].
  destruct (peq (matrix_row d) (matrix_inner_bound d)) as [|RM]; [exact None|].
  destruct (peq (matrix_column d) (matrix_inner_bound d)) as [|CM]; [exact None|].
  destruct (check_index_schedule row_index_order column_index_order) eqn:ORDER; [|exact None].
  exact (Some (@MatrixCertificate source d SOURCE BODY OUTER RN RC NC RM CM ORDER)).
Defined.

Definition checked_matrix_rule {source d} (CERT : matrix_certificate source d) :
  encoded_region_rule source (matrix_described_target d).
Proof.
  rewrite (matrix_source_bound CERT); unfold matrix_described_source, matrix_described_target.
  exact (@matrix_region_rule (described_array d) (matrix_row d) (matrix_bound d) (matrix_column d)
    (matrix_inner_bound d) (matrix_inner_body d) (matrix_outer_body d)
    (matrix_distinct_row_bound CERT) (matrix_distinct_row_column CERT) (matrix_distinct_bound_column CERT)
    (matrix_distinct_row_inner_bound CERT) (matrix_distinct_column_inner_bound CERT)
    (matrix_body_bound CERT) (matrix_outer_bound CERT) (matrix_schedule_bound CERT)).
Defined.

Definition select_matrix_interchange source : option statement :=
  match propose_matrix_description source with
  | Some d => match check_matrix_description source d with
    | Some CERT => Some (generated_region (checked_matrix_rule CERT))
    | None => None end
  | None => None end.

Theorem select_matrix_interchange_sound source target :
  select_matrix_interchange source = Some target -> region_contract source target.
Proof.
  unfold select_matrix_interchange; destruct (propose_matrix_description source) as [d|]; try discriminate.
  destruct (check_matrix_description source d) as [CERT|]; try discriminate.
  intro SELECT; inversion SELECT; subst; apply encoded_region_rule_sound.
Qed.

Definition example_matrix_body := matrix_store 5%positive 1%positive 3%positive.
Definition example_matrix_outer := matrix_row_body 3%positive 4%positive example_matrix_body.
Definition example_matrix_source := frontend_counted_loop 1%positive 2%positive example_matrix_outer.
Example matrix_interchange_selected : exists target, select_matrix_interchange example_matrix_source = Some target.
Proof. eexists; vm_compute; reflexivity. Qed.
Example matrix_interchange_different_value_refused :
  select_matrix_interchange (frontend_counted_loop 1%positive 2%positive
    (matrix_row_body 3%positive 4%positive (Sassign
      (matrix_lvalue 5%positive 1%positive 3%positive) (matrix_constant 99)))) = None.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions select_matrix_interchange_sound.
